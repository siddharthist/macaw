{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Werror #-}
module Data.Macaw.AbsDomain.AbsState
  ( AbsBlockState
  , setAbsIP
  , absRegState
  , absStackHasReturnAddr
  , CallParams(..)
  , absEvalCall
  , AbsBlockStack
  , StackEntry(..)
  , ArchAbsValue
  , AbsValue(..)
  , bvadd
  , emptyAbsValue
  , joinAbsValue
  , ppAbsValue
  , absTrue
  , absFalse
  , subValue
  , concreteStackOffset
  , concretize
  , asConcreteSingleton
  , meet
  , absValueSize
  , codePointerSet
  , AbsDomain(..)
  , AbsProcessorState
  , absMem
  , curAbsStack
  , absInitialRegs
  , indexBounds
  , startAbsStack
  , initAbsProcessorState
  , absAssignments
  , assignLens
  , stridedInterval
  , finalAbsBlockState
  , addMemWrite
  , transferValue
  , abstractULt
  , abstractULeq
  , isBottom
  , transferApp
    -- * Utilities
  , hasMaximum
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Foldable
import           Data.Functor
import           Data.Int
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes (EqF(..), ShowF(..))
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Stack
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.CFG
import           Data.Macaw.DebugLogging
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

------------------------------------------------------------------------
-- Utilities

addOff :: NatRepr w -> Integer -> Integer -> Integer
addOff w o v = toUnsigned w (o + v)

------------------------------------------------------------------------
-- AbsDomain

-- | This represents an lattice order.
--
-- Elements are comparable for equality, have a partial order, a top element,
-- and the ability to join to elements.
class Eq d => AbsDomain d where
  -- | The top element
  top :: d

  -- | A partial ordering over d.  forall x. x `leq` top
  leq :: d -> d -> Bool
  leq x y =
    case joinD y x of
      Nothing -> True
      Just _ -> False

  -- | Least upper bound (always defined, as we have top)
  lub :: d -> d -> d
  lub x y = case joinD x y of
              Nothing -> x
              Just r -> r

  -- | Join the old and new states and return the updated state iff
  -- the result is larger than the old state.
  joinD :: d -> d -> Maybe d
  joinD old new
    | new `leq` old = Nothing
    | otherwise     = Just $ lub old new

  {-# MINIMAL (top, ((leq,lub) | joinD)) #-}

------------------------------------------------------------------------
-- AbsValue

-- | The abstract information that is associated with values of a given type.
--
-- The first parameter is the width of pointers on the value.  It is expected
-- to be at most 64 bits.
data AbsValue w (tp :: Type)
  = (tp ~ BoolType) => BoolConst !Bool
    -- ^ A Boolean constant
  | forall n . (tp ~ BVType n) => FinSet !(Set Integer)
    -- ^ Denotes that this value can take any one of the fixed set.
  | (tp ~ BVType w) => CodePointers !(Set (MemSegmentOff w)) !Bool
     -- ^ Represents that all values point to a bounded set of
     -- addresses in an executable segment or the constant zero.  The
     -- set contains the possible addresses, and the Boolean indicates
     -- whether this set contains the address 0.
  | (tp ~ BVType w) => StackOffset !(MemAddr w) !(Set Int64)
    -- ^ Offset of stack from the beginning of the block at the given address.
    --  First argument is address of block.
  | (tp ~ BVType w) => SomeStackOffset !(MemAddr w)
    -- ^ An offset to the stack at some offset.
  | forall n . (tp ~ BVType n) => StridedInterval !(SI.StridedInterval n)
    -- ^ A strided interval
  | forall n n'
    . ((n + 1) <= n', tp ~ BVType n')
    => SubValue !(NatRepr n) !(AbsValue w (BVType n))
    -- ^ A sub-value about which we know something about the low order bits.
    --
    --e.g., when tp = BVType 16, and n = 8, and the abs value argument is @av@, we
    --know that the lower 8-bits of the value are in @av@, but the upper bits may
    -- be arbitrary.
  | TopV
    -- ^ Any value
  | (tp ~ BVType w) => ReturnAddr
    -- ^ Denotes a return address in the body of a function.

-- | Denotes that we do not know of any value that could be in set.
emptyAbsValue :: AbsValue w (BVType w)
emptyAbsValue = CodePointers Set.empty False

-- | Returns a finite set of values with some width.
data SomeFinSet tp where
  IsFin :: !(Set Integer) -> SomeFinSet (BVType n)
  NotFin :: SomeFinSet tp

-- | Given a segmented addr and flag indicating if zero is contained return the underlying
-- integer set and the set of addresses that had no base.
partitionAbsoluteAddrs :: MemWidth w
                        => Set (MemSegmentOff w)
                        -> Bool
                        -> (Set Integer, Set (MemSegmentOff w))
partitionAbsoluteAddrs addrSet b = foldl' f (s0, Set.empty) addrSet
   where s0 = if b then Set.singleton 0 else Set.empty
         f (intSet,badSet) addr =
           case msegAddr addr of
             Just addrVal -> seq intSet' $ (intSet', badSet)
               where intSet' = Set.insert (toInteger addrVal) intSet
             Nothing -> seq badSet' $ (intSet, badSet')
               where badSet' = Set.insert addr badSet

asFinSet :: forall w tp
         .  MemWidth w
         => String
         -> AbsValue w tp
         -> SomeFinSet tp
asFinSet _ (FinSet s) = IsFin s
asFinSet _ (CodePointers s False)
  | Set.null s = IsFin Set.empty
asFinSet _ (CodePointers s True)
  | Set.null s = IsFin (Set.singleton 0)
asFinSet nm (CodePointers addrSet b) = go (Set.toList addrSet) $! s0
  where s0 = if b then Set.singleton 0 else Set.empty
        go :: [MemSegmentOff w] -> Set Integer -> SomeFinSet (BVType w)
        go [] s = debug DAbsInt ("dropping Codeptr " ++ nm) $ IsFin s
        go (seg_off: r) s =
          case msegAddr seg_off of
            Just addr -> go r $! Set.insert (toInteger addr) s
            Nothing -> NotFin
asFinSet _ _ = NotFin

-- asFinSet64 :: String -> AbsValue (BVType 64) -> Maybe (Set Word64)
-- asFinSet64 _ (FinSet s) = Just $! (Set.mapMonotonic fromInteger s)
-- asFinSet64 nm (CodePointers s)
--   | isZeroPtr s = Just s
--   | otherwise = debug DAbsInt ("dropping Codeptr " ++ nm) $ Just s
-- asFinSet64 _ _ = Nothing

codePointerSet :: AbsValue w tp -> Set (MemSegmentOff w)
codePointerSet (CodePointers s _) = s
codePointerSet _ = Set.empty

-- | The maximum number of values we hold in a value set, after which we move to
-- intervals
maxSetSize :: Int
maxSetSize = 5

-- Note that this is syntactic equality only.
instance Eq (AbsValue w tp) where
  FinSet x    == FinSet y      = x == y
  CodePointers x xb == CodePointers y yb = x == y && xb == yb
  StackOffset ax ox  == StackOffset ay oy   = (ax,ox) == (ay,oy)
  SomeStackOffset ax == SomeStackOffset ay = ax == ay
  StridedInterval si1 == StridedInterval si2 = si1 == si2
  SubValue n v == SubValue n' v'
    | Just Refl <- testEquality n n' = v == v'
    | otherwise = False
  TopV == TopV = True
  ReturnAddr == ReturnAddr = True
  _    == _    = False

instance EqF (AbsValue w) where
  eqF = (==)

instance MemWidth w => Show (AbsValue w tp) where
  show = show . pretty

instance MemWidth w => Pretty (AbsValue w tp) where
  pretty (BoolConst b) = text (show b)
  pretty (FinSet s) = text "finset" <+> ppIntegerSet s
  pretty (CodePointers s b) = text "code" <+> ppSet (s0 ++ sd)
    where s0 = if b then [text "0"] else []
          sd = f <$> Set.toList s
          f segAddr = text (show segAddr)

  pretty (StridedInterval s) =
    text "strided" <> parens (pretty s)
  pretty (SubValue n av) =
    text "sub" <> parens (integer (natValue n) <> comma <+> pretty av)
  pretty (StackOffset a s) = ppSet (ppv <$> Set.toList s)
    where ppv v' | v' >= 0   = text $ "rsp_" ++ show a ++ " + " ++ showHex v' ""
                 | otherwise = text $ "rsp_" ++ show a ++ " - " ++ showHex (negate (toInteger v')) ""

  pretty (SomeStackOffset a) = text $ "rsp_" ++ show a ++ " + ?"
  pretty TopV = text "top"
  pretty ReturnAddr = text "return_addr"

ppSet :: [Doc] -> Doc
ppSet = encloseSep lbrace rbrace comma

ppIntegerSet :: (Integral w, Show w) => Set w -> Doc
ppIntegerSet s = ppSet (ppv <$> Set.toList s)
  where ppv v' | v' >= 0 = text (showHex v' "")
               | otherwise = error "ppIntegerSet given negative value"

-- | Returns a set of concrete integers that this value may be.
-- This function will neither return the complete set or an
-- known under-approximation.
concretize :: MemWidth w => AbsValue w tp -> Maybe (Set Integer)
concretize (FinSet s) = Just s
concretize (CodePointers s b) = Just $ Set.fromList $
  [ toInteger addr
  | mseg <- Set.toList s
  , addr <- maybeToList (msegAddr mseg)
  ]
  ++ (if b then [0] else [])
concretize (SubValue _ _) = Nothing -- we know nothing about _all_ values
concretize (StridedInterval s) =
  debug DAbsInt ("Concretizing " ++ show (pretty s)) $
  Just (Set.fromList (SI.toList s))
concretize (BoolConst b) = Just (Set.singleton (if b then 1 else 0))
concretize SomeStackOffset{} = Nothing
concretize TopV       = Nothing
concretize ReturnAddr = Nothing
concretize StackOffset{} = Nothing

-- FIXME: make total, we would need to carry around tp
absValueSize :: AbsValue w tp -> Maybe Integer
absValueSize (FinSet s) = Just $ fromIntegral (Set.size s)
absValueSize (CodePointers s b) = Just $ fromIntegral (Set.size s) + (if b then 1 else 0)
absValueSize (StridedInterval s) = Just $ SI.size s
absValueSize (StackOffset _ s) = Just $ fromIntegral (Set.size s)
absValueSize (BoolConst _)     = Just 1
absValueSize SomeStackOffset{} = Nothing
absValueSize SubValue{} = Nothing
absValueSize TopV       = Nothing
absValueSize ReturnAddr = Nothing

-- | Returns single value, if the abstract value can only take on one value.
asConcreteSingleton :: MemWidth w => AbsValue w tp -> Maybe Integer
asConcreteSingleton v = do
  sz <- absValueSize v
  guard (sz == 1)
  [i] <- Set.toList <$> concretize v
  return i

-- -----------------------------------------------------------------------------
-- Smart constructors

-- | Smart constructor for strided intervals which takes care of top
stridedInterval :: SI.StridedInterval n -> AbsValue w (BVType n)
stridedInterval si
  | SI.isTop si = TopV
  | otherwise   = StridedInterval si

-- | Smart constructor for sub-values.  This ensures that the
-- subvalues are sorted on size.
subValue :: ((n + 1) <= n')
         => NatRepr n
         -> AbsValue w (BVType n)
         -> AbsValue w (BVType n')
subValue n v
  | TopV <- v = TopV
  | otherwise = SubValue n v

isEmpty :: AbsValue w tp -> Bool
isEmpty (CodePointers s b) = Set.null s && not b
isEmpty (FinSet s) = Set.null s
isEmpty _ = False

-------------------------------------------------------------------------------
-- Joining abstract values

instance MemWidth w => AbsDomain (AbsValue w tp) where
  top = TopV
  joinD = joinAbsValue

-- | Join the old and new states and return the updated state iff
-- the result is larger than the old state.
-- This also returns any addresses that are discarded during joining.
joinAbsValue :: MemWidth w
             => AbsValue w tp
             -> AbsValue w tp
             -> Maybe (AbsValue w tp)
joinAbsValue x y
    | Set.null s = r
    | otherwise = debug DAbsInt ("dropping " ++ show dropped ++ "\n" ++ show x ++ "\n" ++ show y ++ "\n") r
  where (r,s) = runState (joinAbsValue' x y) Set.empty
        dropped = ppSet (text . show <$> Set.toList s)

addWords :: Set (MemSegmentOff w) -> State (Set (MemSegmentOff w)) ()
addWords s = modify $ Set.union s

-- | Join the old and new states and return the updated state iff
-- the result is larger than the old state.
-- This also returns any addresses that are discarded during joining.
joinAbsValue' :: MemWidth w
              => AbsValue w tp
              -> AbsValue w tp
              -> State (Set (MemSegmentOff w)) (Maybe (AbsValue w tp))
joinAbsValue' TopV x = do
  addWords (codePointerSet x)
  return $! Nothing
joinAbsValue' x y | isEmpty y = return $ Nothing
                  | isEmpty x = return $ (Just $! y)
joinAbsValue' (CodePointers old old_b) (CodePointers new new_b)
    | new `Set.isSubsetOf` old && (not new_b || old_b) = return $ Nothing
    | otherwise = return $ (Just $! CodePointers r (old_b || new_b))
  where r = Set.union old new
joinAbsValue' (FinSet old) (CodePointers new_set new_zero)
    | wordSet `Set.isSubsetOf` old = do
      addWords new_set
      return $ Nothing
    | Set.size r > maxSetSize = do
      addWords new_set
      return $ Just TopV
    | otherwise = do
      addWords new_set
      return $ Just (FinSet r)

  where (wordSet,_) = partitionAbsoluteAddrs new_set new_zero
        r = Set.union old wordSet

joinAbsValue' (CodePointers old old_zero) (FinSet new)
    | Set.size r > maxSetSize = do
      addWords old
      return $ Just TopV
    | otherwise = do
      addWords old
      return $ Just (FinSet r)
  where (wordSet,_) = partitionAbsoluteAddrs old old_zero
        r = Set.union wordSet new
joinAbsValue' (FinSet old) (FinSet new)
    | new `Set.isSubsetOf` old = return $ Nothing
    | Set.size r > maxSetSize = return $ Just TopV
    | otherwise = return $ Just (FinSet r)
  where r = Set.union old new
joinAbsValue' (StackOffset a_old old) (StackOffset b_old new)
    | a_old /= b_old = return (Just TopV)
    | new `Set.isSubsetOf` old = return $ Nothing
    | Set.size r > maxSetSize = return $ Just TopV
    | otherwise = return $ Just (StackOffset a_old r)
  where r = Set.union old new
-- Intervals
joinAbsValue' v v'
    | StridedInterval si_old <- v, StridedInterval si_new <- v'
    , si_new `SI.isSubsetOf` si_old =
      return $ Nothing
    | StridedInterval si_old <- v, StridedInterval si_new <- v' =
      return $ go si_old si_new
    | StridedInterval si <- v,  FinSet s <- v' =
      return $ go si (SI.fromFoldable (SI.typ si) s)
    | StridedInterval si <- v,  CodePointers s b <- v' = do
      addWords s
      let (wordSet, _) = partitionAbsoluteAddrs s b
      return $ go si (SI.fromFoldable (SI.typ si) wordSet)
    | FinSet s <- v, StridedInterval si <- v' =
      return $ go si (SI.fromFoldable (SI.typ si) s)
    | StridedInterval si <- v', CodePointers s b <- v = do
      addWords s
      let (wordSet, _) = partitionAbsoluteAddrs s b
      return $ go si (SI.fromFoldable (SI.typ si) wordSet)
  where go si1 si2
           | SI.range si > 10 = Just TopV -- Give up on stride
           | otherwise = Just $ stridedInterval si
          where si = SI.lub si1 si2

-- Sub values
joinAbsValue' (SubValue n av) (SubValue n' av') =
  case testNatCases n n' of
    NatCaseLT LeqProof -> fmap (subValue n) <$> joinAbsValue' av (trunc av' n)
    NatCaseEQ          -> fmap (subValue n) <$> joinAbsValue' av av'
    NatCaseGT LeqProof -> do
      let new_av = trunc av n'
      mv <- joinAbsValue' new_av av'
      return $ Just $! subValue n' (fromMaybe new_av mv)
-- Join addresses
joinAbsValue' (SomeStackOffset ax) (StackOffset ay _) | ax == ay = return $ Nothing
joinAbsValue' (StackOffset ax _) (SomeStackOffset ay)
  | ax == ay = return $ Just (SomeStackOffset ax)
joinAbsValue' (SomeStackOffset ax) (SomeStackOffset ay) | ax == ay = return $ Nothing


joinAbsValue' ReturnAddr ReturnAddr = return Nothing
joinAbsValue' (BoolConst b1) (BoolConst b2)
  | b1 == b2  = return Nothing
  | otherwise = return $! Just TopV

joinAbsValue' x y = do
  addWords (codePointerSet x)
  addWords (codePointerSet y)
  return $! Just TopV

-------------------------------------------------------------------------------
-- Abstract value operations

-- | Return true if the integer value may be an a member of
mayBeMember :: Integer -> AbsValue w (BVType n) -> Bool
mayBeMember _ TopV = True
mayBeMember n (FinSet s) = Set.member n s
mayBeMember 0 (CodePointers _ b) = b
mayBeMember n (StridedInterval si) = SI.member n si
mayBeMember n (SubValue n' v) = mayBeMember (n .&. maxUnsigned n') v
mayBeMember _n _v = True

-- | Returns true if this value represents the empty set.
isBottom :: AbsValue w tp -> Bool
isBottom BoolConst{}      = False
isBottom (FinSet v)       = Set.null v
isBottom (CodePointers v b) = Set.null v && not b
isBottom (StackOffset _ v) = Set.null v
isBottom (SomeStackOffset _) = False
isBottom (StridedInterval v) = SI.size v == 0
isBottom (SubValue _ v) = isBottom v
isBottom TopV = False
isBottom ReturnAddr = False

-------------------------------------------------------------------------------
-- Intersection abstract values

-- meet is probably the wrong word here --- we are really refining the
-- abstract value based upon some new information.  Thus, we want to
-- return an overapproximation rather than an underapproximation of
-- the value.
-- Currently the only case we care about is where v' is an interval

-- @meet x y@ returns an over-approximation of the values in @x@ and @y@.
meet :: MemWidth w
     => AbsValue w tp
     -> AbsValue w tp
     -> AbsValue w tp
meet x y
  | isBottom m
  , not (isBottom x)
  , not (isBottom y) =
      debug DAbsInt ("Got empty: " ++ show (pretty x) ++ " " ++ show (pretty y)) $ m
  | otherwise = m
  where m = meet' x y

meet' :: MemWidth w => AbsValue w tp -> AbsValue w tp -> AbsValue w tp
meet' TopV x = x
meet' x TopV = x
-- FIXME: reuse an old value if possible?
meet' (CodePointers old old_zero) (CodePointers new new_zero) =
  CodePointers (Set.intersection old new) (old_zero && new_zero)
--TODO: Fix below
meet' (asFinSet "meet" -> IsFin old) (asFinSet "meet" -> IsFin new) =
  FinSet $ Set.intersection old new
meet' (StackOffset ax old) (StackOffset ay new) | ax == ay =
  StackOffset ax $ Set.intersection old new

-- Intervals
meet' v v'
  | StridedInterval si_old <- v, StridedInterval si_new <- v'
    = stridedInterval $ si_old `SI.glb` si_new
  | StridedInterval si <- v,  IsFin s <- asFinSet "meet" v'
    = FinSet $ Set.filter (`SI.member` si) s
  | StridedInterval si <- v', IsFin s <- asFinSet "meet" v
    = FinSet $ Set.filter (`SI.member` si) s

-- These cases are currently sub-optimal: really we want to remove all
-- those from the larger set which don't have a prefix in the smaller
-- set.
meet' v v'
  | SubValue n av <- v, SubValue n' av' <- v' =
      case testNatCases n n' of
        NatCaseLT LeqProof -> subValue n av -- FIXME
        NatCaseEQ          -> subValue n (meet av av')
        NatCaseGT LeqProof -> subValue n' av' -- FIXME
  | SubValue n av <- v, IsFin s <- asFinSet "meet" v' =
      FinSet $ Set.filter (\x -> (x .&. maxUnsigned n) `mayBeMember` av) s
  | SubValue n av <- v', IsFin s <- asFinSet "meet" v =
      FinSet $ Set.filter (\x -> (x .&. maxUnsigned n) `mayBeMember` av) s
  | SubValue _ _ <- v, StridedInterval _ <- v' = v' -- FIXME: ?
  | StridedInterval _ <- v, SubValue _ _ <- v' = v -- FIXME: ?

-- Join addresses
meet' (SomeStackOffset ax) s@(StackOffset ay _) = assert (ax == ay) s
meet' s@(StackOffset ax _) (SomeStackOffset ay) | ax == ay = s
meet' (SomeStackOffset ax) (SomeStackOffset ay) = assert (ax == ay) $ SomeStackOffset ax
meet' x _ = x -- Arbitrarily pick one.
-- meet x y = error $ "meet: impossible" ++ show (x,y)

-------------------------------------------------------------------------------
-- Operations

trunc :: (MemWidth w, v+1 <= u)
      => AbsValue w (BVType u)
      -> NatRepr v
      -> AbsValue w (BVType v)
trunc (FinSet s) w       = FinSet (Set.map (toUnsigned w) s)
trunc (CodePointers s b) _ = FinSet sf
  where (sf,_) = partitionAbsoluteAddrs s b
trunc (StridedInterval s) w = stridedInterval (SI.trunc s w)
trunc (SubValue n av) w =
  case testNatCases n w of
   NatCaseLT LeqProof -> SubValue n av
   NatCaseEQ          -> av
   NatCaseGT LeqProof -> trunc av w
trunc (StackOffset _ _)   _ = TopV
trunc (SomeStackOffset _) _ = TopV
trunc ReturnAddr _ = TopV
trunc TopV _ = TopV

uext :: forall u v w
     .  (u+1 <= v, MemWidth w)
     => AbsValue w (BVType u) -> NatRepr v -> AbsValue w (BVType v)
uext (FinSet s) _ = FinSet s
uext (CodePointers s b) _ = FinSet wordSet
  where (wordSet, _) = partitionAbsoluteAddrs s b
uext (StridedInterval si) w =
  StridedInterval $ si { SI.typ = w }
uext (SubValue (n :: NatRepr n) av) _ =
  -- u + 1 <= v, n + 1 <= u, need n + 1 <= v
  -- proof: n + 1 <= u + 1 by addIsLeq
  --        u + 1 <= v     by assumption
  --        n + 1 <= v     by transitivity
  case proof of
    LeqProof -> SubValue n av
  where
    proof :: LeqProof (n + 1) v
    proof = leqTrans (leqAdd (LeqProof :: LeqProof (n+1) u) knownNat) (LeqProof :: LeqProof (u + 1) v)
uext (StackOffset _ _) _ = TopV
uext (SomeStackOffset _) _ = TopV
uext ReturnAddr _ = TopV
uext TopV _ = TopV

asBoolConst :: AbsValue w BoolType -> Maybe Bool
asBoolConst (BoolConst b) = Just b
asBoolConst TopV = Nothing

bvadc :: forall w u
      .  MemWidth w
      => NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
      -> AbsValue w BoolType
      -> AbsValue w (BVType u)
-- Stacks
bvadc w (StackOffset a s) (FinSet t) c
  | [o0] <- Set.toList t
  , BoolConst b <- c
  , o <- if b then o0 + 1 else o0 =
    StackOffset a $ Set.map (fromInteger . addOff w o . toInteger) s
bvadc w (FinSet t) (StackOffset a s) c
  | [o0] <- Set.toList t
  , BoolConst b <- c
  , o <- if b then o0 + 1 else o0 =
    StackOffset a $ Set.map (fromInteger . addOff w o . toInteger) s
-- Two finite sets
bvadc w (FinSet l) (FinSet r) (BoolConst b)
  | ls <- Set.toList l
  , rs <- Set.toList r
  = case Set.fromList [bottomBits $ lval+rval+if b then 1 else 0 | lval <- ls, rval <- rs] of
      s | Set.size s <= maxSetSize -> FinSet s
      _ -> TopV
  where
  bottomBits v = v .&. (bit (fromInteger (natValue w)) - 1)
-- Strided intervals
bvadc w v v' c
  | StridedInterval si1 <- v, StridedInterval si2 <- v' = go si1 si2
  | StridedInterval si <- v,  IsFin s <- asFinSet "bvadc" v' = go si (SI.fromFoldable w s)
  | StridedInterval si <- v', IsFin s <- asFinSet "bvadc" v  = go si (SI.fromFoldable w s)
  where
    go :: SI.StridedInterval u -> SI.StridedInterval u -> AbsValue w (BVType u)
    go si1 si2 = stridedInterval $ SI.bvadc w si1 si2 (asBoolConst c)

-- the rest
bvadc _ (StackOffset ax _)   _ _ = SomeStackOffset ax
bvadc _ _   (StackOffset ax _) _ = SomeStackOffset ax
bvadc _ (SomeStackOffset ax) _ _ = SomeStackOffset ax
bvadc _ _ (SomeStackOffset ax) _ = SomeStackOffset ax
bvadc _ _ _ _ = TopV

bvadd :: forall w u
      .  MemWidth w
      => NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
bvadd w x y = bvadc w x y (BoolConst False)

setL :: Ord a
     => ([a] -> AbsValue w (BVType n))
     -> (Set a -> AbsValue w (BVType n))
     -> [a]
     -> AbsValue w (BVType n)
setL def c l | length l > maxSetSize = def l
             | otherwise = c (Set.fromList l)

-- | Subtracting
bvsbb :: forall w u
      .  MemWidth w
      => Memory w
         -- ^ Memory used for checking code pointers.
      -> NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
      -> AbsValue w BoolType
      -> AbsValue w (BVType u)
bvsbb mem w (CodePointers s b) (FinSet t) (BoolConst False)
      -- If we just have zero.
    | Set.null s && b = FinSet (Set.map (toUnsigned w . negate) t)
    | all isJust vals && (not b || Set.singleton 0 == t) =
      CodePointers (Set.fromList (catMaybes vals)) b
    | otherwise = error "Losing code pointers due to bvsub."
  where vals :: [Maybe (MemSegmentOff w)]
        vals = do
          x <- Set.toList s
          y <- Set.toList t
          let z = relativeSegmentAddr x & incAddr (negate y)
          case asSegmentOff mem z of
            Just z_mseg | segmentFlags (msegSegment z_mseg) `Perm.hasPerm` Perm.execute ->
              pure (Just z_mseg)
            _ ->
              pure Nothing
bvsbb _ _ xv@(CodePointers xs xb) (CodePointers ys yb) (BoolConst False)
      -- If we just have zero.
    | Set.null ys && yb = xv
      --
    | all isJust vals && xb == yb =
        if xb then
          FinSet (Set.insert 0 (Set.fromList (catMaybes vals)))
         else
          FinSet (Set.fromList (catMaybes vals))
    | otherwise = error "Losing code pointers due to bvsub."
  where vals :: [Maybe Integer]
        vals = do
          x <- Set.toList xs
          y <- Set.toList ys
          pure (relativeSegmentAddr x `diffAddr` relativeSegmentAddr y)
bvsbb _ w (FinSet s) (asFinSet "bvsub3" -> IsFin t) (BoolConst b) =
  setL (stridedInterval . SI.fromFoldable w) FinSet $ do
  x <- Set.toList s
  y <- Set.toList t
  return $ toUnsigned w $ (x - y) - (if b then 1 else 0)
bvsbb _ w (StackOffset ax s) (asFinSet "bvsub6" -> IsFin t) (BoolConst False) =
  setL (\_ -> SomeStackOffset ax) (StackOffset ax) $ do
    x <- toInteger <$> Set.toList s
    y <- Set.toList t
    return $! fromInteger (toUnsigned w (x - y))
bvsbb _ _ (StackOffset ax _) _ _ = SomeStackOffset ax
bvsbb _ _ _ (StackOffset _ _) _ = TopV
bvsbb _ _ (SomeStackOffset ax) _ _ = SomeStackOffset ax
bvsbb _ _ _ (SomeStackOffset _) _ = TopV
bvsbb _ _ _ _ _b = TopV -- Keep the pattern checker happy


-- | Subtracting
bvsub :: forall w u
      .  MemWidth w
      => Memory w
         -- ^ Memory used for checking code pointers.
      -> NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
bvsub mem w (CodePointers s b) (FinSet t)
      -- If we just have zero.
    | Set.null s && b = FinSet (Set.map (toUnsigned w . negate) t)
    | all isJust vals && (not b || Set.singleton 0 == t) =
      CodePointers (Set.fromList (catMaybes vals)) b
    | otherwise = error "Losing code pointers due to bvsub."
  where vals :: [Maybe (MemSegmentOff w)]
        vals = do
          x <- Set.toList s
          y <- Set.toList t
          let z = relativeSegmentAddr x & incAddr (negate y)
          case asSegmentOff mem z of
            Just z_mseg | segmentFlags (msegSegment z_mseg) `Perm.hasPerm` Perm.execute ->
              pure (Just z_mseg)
            _ ->
              pure Nothing
bvsub _ _ xv@(CodePointers xs xb) (CodePointers ys yb)
      -- If we just have zero.
    | Set.null ys && yb = xv
      --
    | all isJust vals && xb == yb =
        if xb then
          FinSet (Set.insert 0 (Set.fromList (catMaybes vals)))
         else
          FinSet (Set.fromList (catMaybes vals))
    | otherwise = error "Losing code pointers due to bvsub."
  where vals :: [Maybe Integer]
        vals = do
          x <- Set.toList xs
          y <- Set.toList ys
          pure (relativeSegmentAddr x `diffAddr` relativeSegmentAddr y)
bvsub _ w (FinSet s) (asFinSet "bvsub3" -> IsFin t) =
  setL (stridedInterval . SI.fromFoldable w) FinSet $ do
  x <- Set.toList s
  y <- Set.toList t
  return (toUnsigned w (x - y))
bvsub _ w v v'
  | StridedInterval si1 <- v, StridedInterval si2 <- v' = go si1 si2
  | StridedInterval si <- v,  IsFin s <- asFinSet "bvsub4" v' = go si (SI.fromFoldable w s)
  | StridedInterval si <- v', IsFin s <- asFinSet "bvsub5" v  = go si (SI.fromFoldable w s)
  where
    go _si1 _si2 = TopV -- FIXME
bvsub _ w (StackOffset ax s) (asFinSet "bvsub6" -> IsFin t) =
  setL (\_ -> SomeStackOffset ax) (StackOffset ax) $ do
    x <- toInteger <$> Set.toList s
    y <- Set.toList t
    return $! fromInteger (toUnsigned w (x - y))
bvsub _ _ (StackOffset ax _) _ = SomeStackOffset ax
bvsub _ _ _ (StackOffset _ _) = TopV
bvsub _ _ (SomeStackOffset ax) _ = SomeStackOffset ax
bvsub _ _ _ (SomeStackOffset _) = TopV
bvsub _ _ _ _ = TopV -- Keep the pattern checker happy

bvmul :: forall w u
      .  MemWidth w
      => NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
bvmul w (asFinSet "bvmul" -> IsFin s) (asFinSet "bvmul" -> IsFin t) =
  setL (stridedInterval . SI.fromFoldable w) FinSet $ do
  x <- Set.toList s
  y <- Set.toList t
  return (toUnsigned w (x * y))
bvmul w v v'
  | StridedInterval si1 <- v, StridedInterval si2 <- v' = go si1 si2
  | StridedInterval si <- v,  IsFin s <- asFinSet "bvmul" v' = go si (SI.fromFoldable w s)
  | StridedInterval si <- v', IsFin s <- asFinSet "bvmul" v  = go si (SI.fromFoldable w s)
  where
    go :: SI.StridedInterval u -> SI.StridedInterval u -> AbsValue w (BVType u)
    go si1 si2 = stridedInterval $ SI.bvmul w si1 si2

-- bvmul w (SubValue _n _av c) v' = bvmul w c v'
-- bvmul w v (SubValue _n _av c)  = bvmul w v c

bvmul _ _ _ = TopV

-- FIXME: generalise
bvand :: MemWidth w
      => NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
      -> AbsValue w (BVType u)
bvand _w (asFinSet "bvand" -> IsFin s) (asConcreteSingleton -> Just v) =
  FinSet (Set.map (flip (.&.) v) s)
bvand _w (asConcreteSingleton -> Just v) (asFinSet "bvand" -> IsFin s) =
  FinSet (Set.map ((.&.) v) s)
bvand _ _ _ = TopV

-- FIXME: generalise
bitop :: MemWidth w
      => (Integer -> Integer -> Integer)
      -> NatRepr u
      -> AbsValue w (BVType u)
      -> AbsValue w  (BVType u)
      -> AbsValue w (BVType u)
bitop doOp _w (asFinSet "bvand" -> IsFin s) (asConcreteSingleton -> Just v)
  = FinSet (Set.map (flip doOp v) s)
bitop doOp _w (asConcreteSingleton -> Just v) (asFinSet "bvand" -> IsFin s)
  = FinSet (Set.map (doOp v) s)
bitop _ _ _ _ = TopV

ppAbsValue :: MemWidth w => AbsValue w tp -> Maybe Doc
ppAbsValue TopV = Nothing
ppAbsValue v = Just (pretty v)

-- | Print a list of Docs vertically separated.
instance (MemWidth w, ShowF r) => PrettyRegValue r (AbsValue w) where
  ppValueEq _ TopV = Nothing
  ppValueEq r v = Just (text (showF r) <+> text "=" <+> pretty v)


absTrue :: AbsValue w BoolType
absTrue = BoolConst True

absFalse :: AbsValue w BoolType
absFalse = BoolConst False

-- | This returns the smallest abstract value that contains the
-- given unsigned integer.
abstractSingleton :: MemWidth w
                  => Memory w
                     -- ^ Width of code pointer
                  -> NatRepr n
                  -> Integer
                  -> AbsValue w (BVType n)
abstractSingleton mem w i
  | Just Refl <- testEquality w (memWidth mem)
  , 0 <= i && i <= maxUnsigned w
  , Just sa <- resolveAbsoluteAddr mem (fromInteger i)
  , segmentFlags (msegSegment sa) `Perm.hasPerm` Perm.execute =
    CodePointers (Set.singleton sa) False
  | 0 <= i && i <= maxUnsigned w = FinSet (Set.singleton i)
  | otherwise = error $ "abstractSingleton given bad value: " ++ show i ++ " " ++ show w

concreteStackOffset :: MemAddr w -> Integer -> AbsValue w (BVType w)
concreteStackOffset a o = StackOffset a (Set.singleton (fromInteger o))

------------------------------------------------------------------------
-- Restrictions

hasMaximum :: TypeRepr (BVType w) -> AbsValue p (BVType w) -> Maybe Integer
hasMaximum tp v =
  case v of
    FinSet s | Set.null s -> Nothing
             | otherwise  -> Just $! Set.findMax s
    CodePointers s b | Set.null s -> if b then Just 0 else Nothing
                     | otherwise  -> Just $ case tp of BVTypeRepr n -> maxUnsigned n
    StridedInterval si -> Just (SI.intervalEnd si)
    TopV               -> Just $ case tp of BVTypeRepr n -> maxUnsigned n
    _                  -> Nothing


hasMinimum :: TypeRepr (BVType w) -> AbsValue p (BVType w) -> Maybe Integer
hasMinimum _tp v =
  case v of
   FinSet s       | Set.null s -> Nothing
                  | otherwise  -> Just $! Set.findMin s
   CodePointers s b | Set.null s -> if b then Just 0 else Nothing
   StridedInterval si -> Just $! SI.base si
   _                  -> Just 0

-- | @abstractULt x y@ refines x and y with the knowledge that @x < y@
-- is unsigned.
-- For example, given {2, 3} and {2, 3, 4}, we know (only) that
-- {2, 3} and {3, 4} because we may pick any element from either set.

abstractULt :: MemWidth w
            => TypeRepr tp
            -> AbsValue w tp
            -> AbsValue w tp
            -> (AbsValue w tp, AbsValue w tp)
abstractULt _tp TopV TopV = (TopV, TopV)
abstractULt tp@(BVTypeRepr n) x y
  | Just u_y <- hasMaximum tp y
  , Just l_x <- hasMinimum tp x =
    -- debug DAbsInt' ("abstractLt " ++ show (pretty x) ++ " " ++ show (pretty y) ++ " -> ")
    ( meet x (stridedInterval $ SI.mkStridedInterval n False 0 (u_y - 1) 1)
    , meet y (stridedInterval $ SI.mkStridedInterval n False (l_x + 1)
                                                     (maxUnsigned n) 1))

abstractULt _tp x y = (x, y)

-- | @abstractULeq x y@ refines x and y with the knowledge that @x <= y@
abstractULeq :: MemWidth w
             => TypeRepr tp
             -> AbsValue w tp
             -> AbsValue w tp
             -> (AbsValue w tp, AbsValue w tp)
abstractULeq _tp TopV TopV = (TopV, TopV)
abstractULeq tp@(BVTypeRepr n) x y
  | Just u_y <- hasMaximum tp y
  , Just l_x <- hasMinimum tp x =
    ( meet x (stridedInterval $ SI.mkStridedInterval n False 0 u_y 1)
    , meet y (stridedInterval $ SI.mkStridedInterval n False l_x
                                                     (maxUnsigned n) 1))

abstractULeq _tp x y = (x, y)

------------------------------------------------------------------------
-- AbsBlockStack

data StackEntry w
   = forall tp . StackEntry !(MemRepr tp) !(AbsValue w tp)

instance Eq (StackEntry w) where
  StackEntry x_tp x_v == StackEntry y_tp y_v
    | Just Refl <- testEquality x_tp y_tp = x_v == y_v
    | otherwise = False

-- | The AbsBlockStack describes offsets of the stack.
-- Values that are not in the map may denote any values.
-- The stack grows down, so nonegative keys are those within
-- rsp.
type AbsBlockStack w = Map Int64 (StackEntry w)

-- absStackLeq :: AbsBlockStack -> AbsBlockStack -> Bool
-- absStackLeq x y = all entryLeq (Map.toList y)
--   where entryLeq (o, StackEntry y_tp y_v) =
--           case Map.lookup o x of
--             Just (StackEntry x_tp x_v) | Just Refl <- testEquality x_tp y_tp ->
--               isNothing (joinAbsValue y_v x_v)
--             _ -> False

-- | @absStackJoinD y x@ returns the stack containing the union @z@ of the
-- values in @y@ and @x@.  It sets the first state parameter to true if @z@
-- is different from @y@ and adds and escaped code pointers to the second
-- parameter.
absStackJoinD :: MemWidth w
              => AbsBlockStack w
              -> AbsBlockStack w
              -> State (Bool,Set (MemSegmentOff w)) (AbsBlockStack w)
absStackJoinD y x = do
  -- This attempts to merge information from the new state into the old state.
  let entryLeq (o, StackEntry y_tp y_v) =
        case Map.lookup o x of
          -- The new state contains a valuewith the same type.
          Just (StackEntry x_tp x_v) | Just Refl <- testEquality x_tp y_tp -> do
            s <- use _2
            -- Attempt to merge values
            case runState (joinAbsValue' y_v x_v) s of
              -- If merging returns the value y_v, then keep it.
              (Nothing,  s') -> do
                _2 .= s'
                return $ Just (o, StackEntry y_tp y_v)
              -- Otherwise merging returned a new value.
              (Just z_v, s') -> do
                case y_v of
                  ReturnAddr -> debug DAbsInt ("absStackJoinD dropping return value:\n"
                                    ++ "Old state: " ++ show (ppAbsStack y)
                                    ++ "New state: " ++ show (ppAbsStack x)) $
                    return ()
                  _ -> return ()
                _1 .= True
                _2 .= s'
                return $ Just (o, StackEntry y_tp z_v)
          _ -> do
            case y_v of
              ReturnAddr ->
                debug DAbsInt ("absStackJoinD dropping return value:"
                               ++ "\nOld state: " ++ show (ppAbsStack y)
                               ++ "\nNew state: " ++ show (ppAbsStack x)) $
                return ()
              _ -> return ()
            _1 .= True
            _2 %= Set.union (codePointerSet y_v)
            return Nothing
  z <- mapM entryLeq (Map.toList y)
  return $! Map.fromList (catMaybes z)

showSignedHex :: Integer -> ShowS
showSignedHex x | x < 0 = showString "-0x" . showHex (negate x)
                | otherwise = showString "0x" . showHex x

ppAbsStack :: MemWidth w => AbsBlockStack w -> Doc
ppAbsStack m = vcat (pp <$> Map.toDescList m)
  where pp (o,StackEntry _ v) = text (showSignedHex (toInteger o) " :=") <+> pretty v

------------------------------------------------------------------------
-- AbsBlockState

-- | Processor/memory state after at beginning of a block.
data AbsBlockState r
   = AbsBlockState { _absRegState :: !(RegState r (AbsValue (RegAddrWidth r)))
                   , _startAbsStack :: !(AbsBlockStack (RegAddrWidth r))
                   , _initIndexBounds :: !(Jmp.InitialIndexBounds r)
                   }

deriving instance MapF.OrdF r => Eq (AbsBlockState r)

absRegState :: Simple Lens (AbsBlockState r)
                           (RegState r (AbsValue (RegAddrWidth r)))
absRegState = lens _absRegState (\s v -> s { _absRegState = v })

startAbsStack :: Simple Lens (AbsBlockState r) (AbsBlockStack (RegAddrWidth r))
startAbsStack = lens _startAbsStack (\s v -> s { _startAbsStack = v })

initIndexBounds :: Simple Lens (AbsBlockState r) (Jmp.InitialIndexBounds r)
initIndexBounds = lens _initIndexBounds (\s v -> s { _initIndexBounds = v })

instance ( RegisterInfo r
         )
      => AbsDomain (AbsBlockState r) where

  top = AbsBlockState { _absRegState = mkRegState (\_ -> TopV)
                      , _startAbsStack = Map.empty
                      , _initIndexBounds = Jmp.arbitraryInitialBounds
                      }

  joinD x y | regs_changed = Just $! z
            | otherwise = Nothing
    where xs = x^.absRegState
          ys = y^.absRegState

          x_stk = x^.startAbsStack
          y_stk = y^.startAbsStack

          (z,(regs_changed,_dropped)) = flip runState (False, Set.empty) $ do
            z_regs <- mkRegStateM $ \r -> do
              let xr = xs^.boundValue r
              (c,s) <- get
              case runState (joinAbsValue' xr (ys^.boundValue r)) s of
                (Nothing,s') -> do
                  seq s' $ put $ (c,s')
                  return $! xr
                (Just zr,s') -> do
                  seq s' $ put $ (True,s')
                  return $! zr
            z_stk <- absStackJoinD x_stk y_stk
            z_bnds <-
              case Jmp.joinInitialBounds (x^.initIndexBounds) (y^.initIndexBounds) of
                Just z_bnds  -> (_1 .= True) $> z_bnds
                Nothing -> pure (x^.initIndexBounds)

            return $ AbsBlockState { _absRegState     = z_regs
                                   , _startAbsStack   = z_stk
                                   , _initIndexBounds = z_bnds
                                   }

instance ( ShowF r
         , MemWidth (RegAddrWidth r)
         ) => Pretty (AbsBlockState r) where
  pretty s =
      text "registers:" <$$>
      indent 2 (pretty (s^.absRegState)) <$$>
      stack_d <$$>
      jmp_bnds
    where stack = s^.startAbsStack
          stack_d | Map.null stack = empty
                  | otherwise = text "stack:" <$$>
                                indent 2 (ppAbsStack stack)
          jmp_bnds = pretty (s^.initIndexBounds)

instance (ShowF r, MemWidth (RegAddrWidth r)) => Show (AbsBlockState r) where
  show = show . pretty

-- | Update the block state to point to a specific IP address.
setAbsIP :: RegisterInfo r
         => MemSegmentOff (RegAddrWidth r)
            -- ^ The address to set.
         -> AbsBlockState r
         -> AbsBlockState r
setAbsIP a b
    -- Check to avoid reassigning next IP if it is not needed.
  | CodePointers s False <- b^.absRegState^.curIP
  , Set.size s == 1
  , Set.member a s =
    b
  | otherwise =
    b & absRegState . curIP .~ CodePointers (Set.singleton a) False

------------------------------------------------------------------------
-- AbsProcessorState

-- | The absolute value associated with a given architecture.
--
-- This is only a function of the address width.
type ArchAbsValue arch = AbsValue (RegAddrWidth (ArchReg arch))

-- | This stores the abstract state of the system which may be within
-- a block.
data AbsProcessorState r ids
   = AbsProcessorState { absMem       :: !(Memory (RegAddrWidth r))
                         -- ^ Recognizer for code addresses.
                       , _absInitialRegs
                         :: !(RegState r (AbsValue (RegAddrWidth r)))
                         -- ^ Default values of registers
                       , _absAssignments :: !(MapF (AssignId ids) (AbsValue (RegAddrWidth r)))
                         -- ^ The assignments that have been seen, and the
                         -- symbolic values associated with them
                       , _curAbsStack    :: !(AbsBlockStack (RegAddrWidth r))
                         -- ^ The current symbolic state of the stack
                       ,  _indexBounds :: !(Jmp.IndexBounds r ids)
                       }

absInitialRegs :: Simple Lens (AbsProcessorState r ids)
                              (RegState r (AbsValue (RegAddrWidth r)))
absInitialRegs = lens _absInitialRegs (\s v -> s { _absInitialRegs = v })

absAssignments :: Simple Lens (AbsProcessorState r ids)
                              (MapF (AssignId ids) (AbsValue (RegAddrWidth r)))
absAssignments = lens _absAssignments (\s v -> s { _absAssignments = v })

curAbsStack :: Simple Lens (AbsProcessorState r ids) (AbsBlockStack (RegAddrWidth r))
curAbsStack = lens _curAbsStack (\s v -> s { _curAbsStack = v })

-- | Return the index
indexBounds :: Simple Lens (AbsProcessorState r ids) (Jmp.IndexBounds r ids)
indexBounds = lens _indexBounds (\s v -> s { _indexBounds = v })


instance (ShowF r, MemWidth (RegAddrWidth r))
      => Pretty (AbsProcessorState r ids) where
  pretty s =
      text "registers:" <$$>
      indent 2 (pretty (s^.absInitialRegs)) <$$>
      stack_d
    where stack = s^.curAbsStack
          stack_d | Map.null stack = empty
                  | otherwise = text "stack:" <$$>
                                indent 2 (ppAbsStack stack)

instance (ShowF r, MemWidth (RegAddrWidth r))
      => Show (AbsProcessorState r ids) where
  show = show . pretty

initAbsProcessorState :: Memory (RegAddrWidth r)
                         -- ^ Current state of memory in the processor.
                         --
                         -- Used for checking code segment status.
                      -> AbsBlockState r
                      -> AbsProcessorState r ids
initAbsProcessorState mem s =
  AbsProcessorState { absMem = mem
                    , _absInitialRegs = s^.absRegState
                    , _absAssignments = MapF.empty
                    , _curAbsStack = s^.startAbsStack
                    , _indexBounds = Jmp.mkIndexBounds (s^.initIndexBounds)
                    }

-- | A lens that allows one to lookup and update the value of an assignment in
-- map from assignments to abstract values.
assignLens :: AssignId ids tp
           -> Simple Lens (MapF (AssignId ids) (AbsValue w)) (AbsValue w tp)
assignLens ass = lens (fromMaybe TopV . MapF.lookup ass)
                      (\s v -> MapF.insert ass v s)

deleteRange :: Int64 -> Int64 -> AbsBlockStack w -> AbsBlockStack w
deleteRange l h m
  | h <= l = m
  | otherwise =
    case Map.lookupGE l m of
      Just (k,v)
        | k < h
        , StackEntry _ ReturnAddr <- v ->
          debug DAbsInt ("Failing to delete return address at offset " ++ show (k,l,h))
                (deleteRange (k+1) h m)
        | k < h ->
          deleteRange (k+1) h (Map.delete k m)
      _ -> m

-- | Prune stack based on write that may modify stack.
pruneStack :: AbsBlockStack w -> AbsBlockStack w
pruneStack = Map.filter f
  where f (StackEntry _ ReturnAddr) = True
        f _ = False

------------------------------------------------------------------------
-- Transfer Value

-- | Compute abstract value from value and current registers.
transferValue :: forall a ids tp
              .  ( RegisterInfo (ArchReg a)
                 , HasCallStack
                 )
              => AbsProcessorState (ArchReg a) ids
              -> Value a ids tp
              -> ArchAbsValue a tp
transferValue c v = do
  case v of
    BoolValue b -> BoolConst b
    BVValue w i
      | 0 <= i && i <= maxUnsigned w -> abstractSingleton (absMem c) w i
      | otherwise -> error $ "transferValue given illegal value " ++ show (pretty v)
    ThisFunctionAddr _ -> TopV
    -- TODO: Ensure a relocatable value is in code.
    RelocatableValue _w i
      | Just addr <- asSegmentOff (absMem c) i
      , segmentFlags (msegSegment addr) `Perm.hasPerm` Perm.execute ->
        CodePointers (Set.singleton addr) False
      | Just addr <- asAbsoluteAddr i ->
        FinSet $ Set.singleton $ toInteger addr
      | otherwise ->
        TopV
    SymbolValue{} -> TopV
    -- Invariant: v is in m
    AssignedValue a ->
      fromMaybe (error $ "Missing assignment for " ++ show (assignId a))
                (MapF.lookup (assignId a) (c^.absAssignments))
    Initial r -> c^.absInitialRegs ^. boundValue r

------------------------------------------------------------------------
-- Operations

addMemWrite :: ( RegisterInfo (ArchReg arch)
               , MemWidth (ArchAddrWidth arch)
               , HasCallStack
               )
            => BVValue arch ids (ArchAddrWidth arch)
               -- ^ Address that we are writing to.
            -> MemRepr tp
               -- ^ Information about how value should be represented in memory.
            -> Value arch ids tp
               -- ^ Value to write to memory
            -> AbsProcessorState (ArchReg arch) ids
               -- ^ Current processor state.
            -> AbsProcessorState (ArchReg arch) ids
addMemWrite a memRepr v r =
  case (transferValue r a, transferValue r v) of
    -- (_,TopV) -> r
    -- We overwrite _some_ stack location.  An alternative would be to
    -- update everything with v.
    (SomeStackOffset _, _) -> do
      let cur_ip = r^.absInitialRegs^.curIP
      debug DAbsInt ("addMemWrite: dropping stack at "
             ++ show (pretty cur_ip)
             ++ " via " ++ show (pretty a)
             ++" in SomeStackOffset case") $
        r & curAbsStack %~ pruneStack
    (StackOffset _ s, v_abs) ->
      let w = fromInteger (memReprBytes memRepr)
          e = StackEntry memRepr v_abs
          stk0 = r^.curAbsStack
          -- Delete information about old assignment
          stk1 = Set.fold (\o m -> deleteRange o (o+w) m) stk0 s
          -- Add information about new assignment
          stk2 =
            case Set.toList s of
              [o] | v_abs /= TopV -> Map.insert o e stk1
              _ -> stk1
       in r & curAbsStack .~ stk2
    -- FIXME: nuke stack on an unknown address or Top?
    _ -> r

absStackHasReturnAddr :: AbsBlockState r -> Bool
absStackHasReturnAddr s = isJust $ find isReturnAddr (Map.elems (s^.startAbsStack))
  where isReturnAddr (StackEntry _ ReturnAddr) = True
        isReturnAddr _ = False


-- | Return state for after value has run.
finalAbsBlockState :: forall a ids
                   .  ( RegisterInfo (ArchReg a)
                      , MemWidth (ArchAddrWidth a)
                      , HasCallStack
                      )
                   => AbsProcessorState (ArchReg a) ids
                   -> RegState (ArchReg a) (Value a ids)
                      -- ^  Final values for abstract processor state
                   -> AbsBlockState (ArchReg a)
finalAbsBlockState c s =
  let transferReg :: ArchReg a tp -> ArchAbsValue a tp
      transferReg r = transferValue c (s^.boundValue r)
   in AbsBlockState { _absRegState = mkRegState transferReg
                    , _startAbsStack = c^.curAbsStack
                    , _initIndexBounds = Jmp.nextBlockBounds (c^.indexBounds) s
                    }

------------------------------------------------------------------------
-- Transfer functions

transferApp :: forall a ids tp
            .  ( RegisterInfo (ArchReg a)
               , HasCallStack
               )
            => AbsProcessorState (ArchReg a) ids
            -> App (Value a ids) tp
            -> ArchAbsValue a tp
transferApp r a = do
  let t :: Value a ids utp -> ArchAbsValue a utp
      t = transferValue r
  case a of
    Trunc v w -> trunc (t v) w
    UExt  v w -> uext  (t v) w
    BVAdd w x y -> bvadd w (t x) (t y)
    BVAdc w x y c -> bvadc w (t x) (t y) (t c)
    BVSub w x y -> bvsub (absMem r) w (t x) (t y)
    BVSbb w x y b -> bvsbb (absMem r) w (t x) (t y) (t b)
    BVMul w x y -> bvmul w (t x) (t y)
    BVAnd w x y -> bvand w (t x) (t y)
    BVOr w x y  -> bitop (.|.) w (t x) (t y)
    BVShl w v s -> bitop (\x1 x2 -> shiftL x1 (fromInteger x2)) w (t v) (t s)
    _ -> TopV

-- | Minimal information needed to parse a function call/system call
data CallParams (r :: Type -> *)
   = CallParams { postCallStackDelta :: Integer
                  -- ^ Amount stack should shift by when going before/after call.
                , preserveReg        :: forall tp . r tp -> Bool
                  -- ^ Return true if a register value is preserved by a call.
                }

-- | Return state post call
absEvalCall :: forall r
                 .  ( RegisterInfo r
                    , HasRepr r TypeRepr
                    )
                 => CallParams r
                    -- ^ Configuration
                 -> AbsBlockState r
                    -- ^ State before call
                 -> MemSegmentOff (RegAddrWidth r)
                    -- ^ Address we are jumping to
                 -> AbsBlockState r
absEvalCall params ab0 addr =
    AbsBlockState { _absRegState = mkRegState regFn
                  , _startAbsStack = ab0^.startAbsStack
                  , _initIndexBounds = Jmp.arbitraryInitialBounds
                  }
  where regFn :: r tp -> AbsValue (RegAddrWidth r) tp
        regFn r
          -- We set IPReg
          | Just Refl <- testEquality r ip_reg =
              CodePointers (Set.singleton addr) False
          | Just Refl <- testEquality r sp_reg =
              let w = typeWidth r
               in bvadd w (ab0^.absRegState^.boundValue r)
                          (FinSet (Set.singleton (postCallStackDelta params)))
            -- Copy callee saved registers
          | preserveReg params r =
            ab0^.absRegState^.boundValue r
            -- We know nothing about other registers.
          | otherwise =
            TopV
