{-
Copyright        : (c) Galois, Inc 2017-2018
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This provides a facility for disassembling x86 instructions from a
Macaw memory object.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.X86.Flexdis
  ( disassemble
  , DisassembleError(..)
  ) where

import           Control.Monad.Except
import           Control.Monad.State.Strict
import qualified Data.ByteString as BS
import           Data.Int

import           Data.Macaw.Memory

import qualified Flexdis86 as Flexdis
import           Flexdis86.ByteReader

------------------------------------------------------------------------
-- MemStream

-- | A stream of memory
data MemStream w = MS { msOffset :: !Int
                        -- ^ The current offset in the instruction
                      , msNext :: ![SegmentRange w]
                        -- ^ The next bytes to read.
                      }

------------------------------------------------------------------------
-- DisassembleError

data DisassembleError w
   = FlexdisInsufficientBytes
     -- ^ Insufficient bytes to read instruction
   | FlexdisUnexpectedBSS
     -- ^ Instruction read into BSS region.
   | FlexdisUnexpectedRelocation !(Relocation w)
   | FlexdisInvalidInstruction

instance Show (DisassembleError w) where
  show FlexdisInsufficientBytes = "Unexpected end of address space."
  show FlexdisUnexpectedBSS  = "Cannot disassemble BSS region."
  show (FlexdisUnexpectedRelocation r) =
    "Unexpected relocation: " ++ show r
  show FlexdisInvalidInstruction = "Invalid instruction"

------------------------------------------------------------------------
-- MemoryByteReader

newtype MemoryByteReader w a
  = MBR { unMBR :: ExceptT (DisassembleError w) (State (MemStream w)) a }
  deriving (Functor, Applicative, MonadError (DisassembleError w))

instance Monad (MemoryByteReader w) where
  return = MBR . return
  MBR m >>= f = MBR $ m >>= unMBR . f
  fail msg = error $ "Internal MemoryByteReader error: " ++ msg

-- | Run a memory byte reader starting from the given offset and offset for next.
runMemoryByteReader :: [SegmentRange w] -- ^ Data to read next.
                    -> MemoryByteReader w a -- ^ Byte reader to read values from.
                    -> (Either (DisassembleError w) a, MemStream w)
runMemoryByteReader contents (MBR m) = do
  let ms0 = MS { msOffset = 0
               , msNext   = contents
               }
  runState (runExceptT m) ms0

bsInt8 :: BS.ByteString -> Int8
bsInt8 = fromIntegral . bsWord8

bsInt16le :: BS.ByteString -> Int16
bsInt16le = fromIntegral . bsWord16le

bsInt32le :: BS.ByteString -> Int32
bsInt32le = fromIntegral . bsWord32le

-- | Read bytes from a jump table.
jumpSizeByteCount :: Flexdis.JumpSize -> Int
jumpSizeByteCount sz =
  case sz of
    Flexdis.JSize8  -> 1
    Flexdis.JSize16 -> 2
    Flexdis.JSize32 -> 4

-- | Read bytes from a jump table.
interpJumpBytes :: Flexdis.JumpSize -> BS.ByteString -> Int64
interpJumpBytes sz =
  case sz of
    Flexdis.JSize8  -> fromIntegral . bsInt8
    Flexdis.JSize16 -> fromIntegral . bsInt16le
    Flexdis.JSize32 -> fromIntegral . bsInt32le

updateMSByteString :: MemStream w
                   -> BS.ByteString
                   -> [SegmentRange w]
                   -> Int
                   -> MemoryByteReader w ()
updateMSByteString ms bs rest c = do
  when (BS.length bs < c) $ insufficientBytes rest
  let bs' = BS.drop c bs
  let ms' = ms { msOffset = msOffset ms + c
               , msNext   =
                 if BS.null bs' then
                   rest
                  else
                   ByteRegion bs' : rest
               }
  seq ms' $ MBR $ put ms'

unsupportedRelocation :: Relocation w -> MemoryByteReader w a
unsupportedRelocation =
  throwError . FlexdisUnexpectedRelocation

-- | Report an error that we cannot read bytes because of some other regio.
insufficientBytes :: [SegmentRange w] -> MemoryByteReader w a
insufficientBytes rest =
  case rest of
    [] -> throwError FlexdisInsufficientBytes
    -- Throw error if we try to read a relocation as a symbolic reference
    BSSRegion _:_ -> throwError FlexdisUnexpectedBSS
    RelocationRegion r:_ -> throwError $ FlexdisUnexpectedRelocation r
    ByteRegion _:_ -> error $ "Memory contents contains adjacent byte regions."

readBytes :: Int -> MemoryByteReader w BS.ByteString
readBytes 0 = pure BS.empty
readBytes c = do
  ms <- MBR get
  -- If remaining bytes are empty
  case msNext ms of
    [] ->
      throwError FlexdisInsufficientBytes
    -- Throw error if we try to read a relocation as a symbolic reference
    BSSRegion _:_ -> do
      throwError FlexdisUnexpectedBSS
    RelocationRegion r:_ ->
      throwError $ FlexdisUnexpectedRelocation r
    ByteRegion bs:rest -> do
      updateMSByteString ms bs rest c
      pure $! bs


instance MemWidth w => ByteReader (MemoryByteReader w) where
  readByte = BS.head <$> readBytes 1

  readDImm = do
    ms <- MBR get
    -- If remaining bytes are empty
    case msNext ms of
      [] ->
        throwError FlexdisInsufficientBytes
      -- Throw error if we try to read a relocation as a symbolic reference
      BSSRegion _:_ -> do
        throwError FlexdisUnexpectedBSS
      RelocationRegion r:rest -> do
        let sym = relocationSym r
        let off = relocationOffset r
        let isGood
              =  relocationIsRel r == False
              && relocationSize r == 4
              && relocationEndianness r == LittleEndian
        when (not isGood) $ do
          unsupportedRelocation r
        -- Returns whether the bytes in this relocation are thought of as signed or unsigned.
        let signed = relocationIsSigned r

        let ms' = ms { msOffset = msOffset ms + 4
                     , msNext   = rest
                     }
        seq ms' $ MBR $ put ms'
        pure $ Flexdis.Imm32SymbolOffset sym (fromIntegral off) signed

      ByteRegion bs:rest -> do
        updateMSByteString ms bs rest 4
        let v = bsWord32le (BS.take 4 bs)
        pure $! Flexdis.Imm32Concrete (fromIntegral v)

  readJump jumpType = do
    ms <- MBR get
    -- If remaining bytes are empty
    case msNext ms of
      [] ->
        throwError FlexdisInsufficientBytes
      -- Throw error if we try to read a relocation as a symbolic reference
      BSSRegion _:_ -> do
        throwError FlexdisUnexpectedBSS
      RelocationRegion r:rest -> do
        let jsize = jumpSizeByteCount jumpType
        -- Sanity checks
        let isGood
              =  relocationIsRel r
              && relocationSize r == jsize
              && relocationIsSigned r == False
              && relocationEndianness r == LittleEndian
        when (not isGood) $ do
          throwError $ FlexdisUnexpectedRelocation r

        let ms' = ms { msOffset = msOffset ms + jsize
                     , msNext   = rest
                     }
        seq ms' $ MBR $ put ms'
        let ioff = fromIntegral (msOffset ms)
        let sym = relocationSym r
        pure $ Flexdis.RelativeOffset ioff sym (fromIntegral (relocationOffset r))

{-
        unsupportedRelocation r

-}
      ByteRegion bs:rest -> do
        let c = jumpSizeByteCount jumpType
        updateMSByteString ms bs rest (fromIntegral c)
        pure $! Flexdis.FixedOffset (interpJumpBytes jumpType (BS.take c bs))


  invalidInstruction = do
    throwError $ FlexdisInvalidInstruction

------------------------------------------------------------------------
-- readInstruction

-- | Read instruction at a given memory address.
--
-- This returns the number of bytes in the instruction, the
-- instruction instance, and the remaining contents, or an error and
-- the offset within the region that the bytes occurred.
disassemble :: [SegmentRange 64] -- ^ Data to read next.
            -> Either (Int, DisassembleError 64)
                      (Int, Flexdis.InstructionInstance, [SegmentRange 64])
disassemble contents = do
  case runMemoryByteReader contents Flexdis.disassembleInstruction of
    (Left err, ms) ->
      Left $ (msOffset ms, err)
    (Right i, ms) -> Right (msOffset ms, i, msNext ms)
