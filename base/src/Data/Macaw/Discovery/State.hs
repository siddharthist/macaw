{-|
Copyright  : (c) Galois, Inc 2016-2018
Maintainer : jhendrix@galois.com

This defines the main data structure for storing information learned from code
discovery.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.Discovery.State
  ( GlobalDataInfo(..)
  , ParsedTermStmt(..)
  , StatementList(..)
  , ParsedBlock(..)
    -- * The interpreter state
  , DiscoveryState
  , AddrSymMap
  , exploredFunctions
  , ppDiscoveryStateBlocks
  , emptyDiscoveryState
  , memory
  , symbolNames
  , archInfo
  , globalDataMap
  , funInfo
  , unexploredFunctions
  , trustedFunctionEntryPoints
  , exploreFnPred
    -- * DiscoveryFunInfo
  , DiscoveryFunInfo(..)
  , parsedBlocks
    -- * Reasons for exploring
  , FunctionExploreReason(..)
  , BlockExploreReason(..)
    -- * DiscoveryState utilities
  , RegConstraint
  )  where

import           Control.Lens
import qualified Data.ByteString.Char8 as BSC
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.AbsDomain.AbsState
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.Types

------------------------------------------------------------------------
-- AddrSymMap

-- | Maps code addresses to the associated symbol name if any.
type AddrSymMap w = Map.Map (MemSegmentOff w) BSC.ByteString

------------------------------------------------------------------------
-- BlockExploreReason

-- | This describes why we started exploring a given function.
data FunctionExploreReason w
     -- | Exploring because code at the given block writes it to memory.
  = PossibleWriteEntry !(MemSegmentOff w)
    -- | Exploring because address terminates with a call that jumps here.
  | CallTarget !(MemSegmentOff w)
    -- | Identified as an entry point from initial information
  | InitAddr
    -- | A code pointer that was stored at the given address.
  | CodePointerInMem !(MemSegmentOff w)
    -- | The user requested that we analyze this address as a function.
  | UserRequest
  deriving (Eq, Show)

------------------------------------------------------------------------
-- BlockExploreReason

-- | This describes why we are exploring a given block within a function.
data BlockExploreReason w
     -- | Exploring because the given block writes it to memory.
  --  =- InWrite !(MemSegmentOff w)
     -- | Exploring because the given block jumps here.
   = NextIP !(MemSegmentOff w)
     -- | Identified as an entry point from initial information
   | FunctionEntryPoint
     -- | Added because the address split this block after it had been
     -- disassembled.  Also includes the reason we thought the block
     -- should be there before we split it.
   | SplitAt !(MemSegmentOff w) !(BlockExploreReason w)
     -- The user requested that we analyze this address as a function.
     -- UserRequest
  deriving (Eq, Show)

------------------------------------------------------------------------
-- GlobalDataInfo

-- | Information about a region of memory.
data GlobalDataInfo w
  -- | A jump table that appears to end just before the given address.
  = JumpTable !(Maybe w)
  -- | A value that appears in the program text.
  | ReferencedValue

instance (Integral w, Show w) => Show (GlobalDataInfo w) where
  show (JumpTable Nothing) = "unbound jump table"
  show (JumpTable (Just w)) | w >= 0 = "jump table end " ++ showHex w ""
                            | otherwise = error "jump table with negative offset given"
  show ReferencedValue = "global addr"

------------------------------------------------------------------------
-- ParsedTermStmt

-- | This term statement is used to describe higher level expressions
-- of how block ending with a a FetchAndExecute statement should be
-- interpreted.
data ParsedTermStmt arch ids
  -- | A call with the current register values and location to return to or 'Nothing'  if this is a tail call.
  = ParsedCall !(RegState (ArchReg arch) (Value arch ids))
               !(Maybe (ArchSegmentOff arch))
    -- | @PLTStub regs addr@ denotes a terminal statement that has been identified as a PLT stub
    -- for calling the given relocation.
    --
    -- This is a special case of a tail call.  It has been added
    -- separately because it occurs frequently in dynamically linked
    -- code, and we can use this to recognize PLT stubs.
    --
    -- The register set only contains registers that were changed in
    -- the function.  Other registers have the initial value.
  | PLTStub !(MapF.MapF (ArchReg arch) (Value arch ids))
            !(ArchSegmentOff arch)
            !(Relocation (ArchAddrWidth arch))
  -- | A jump to an explicit address within a function.
  | ParsedJump !(RegState (ArchReg arch) (Value arch ids)) !(ArchSegmentOff arch)
  -- | A lookup table that branches to one of a vector of addresses.
  --
  -- The registers store the registers, the value contains the index to jump
  -- to, and the possible addresses as a table.  If the index (when interpreted as
  -- an unsigned number) is larger than the number of entries in the vector, then the
  -- result is undefined.
  | ParsedLookupTable !(RegState (ArchReg arch) (Value arch ids))
                      !(ArchAddrValue arch ids)
                      !(V.Vector (ArchSegmentOff arch))
  -- | A return with the given registers.
  | ParsedReturn !(RegState (ArchReg arch) (Value arch ids))
  -- | An if-then-else
  | ParsedIte !(Value arch ids BoolType) !(StatementList arch ids) !(StatementList arch ids)
  -- | An architecture-specific statement with the registers prior to execution, and
  -- the given next control flow address.
  | ParsedArchTermStmt !(ArchTermStmt arch ids)
                       !(RegState (ArchReg arch) (Value arch ids))
                       !(Maybe (ArchSegmentOff arch))
  -- | An error occured in translating the block
  | ParsedTranslateError !Text
  -- | The classifier failed to identity the block.
  | ClassifyFailure !(RegState (ArchReg arch) (Value arch ids))

-- | Pretty print the block contents indented inside brackets.
ppStatementList :: ArchConstraints arch => (ArchAddrWord arch -> Doc) -> StatementList arch ids -> Doc
ppStatementList ppOff b =
  text "{" <$$>
  indent 2 (vcat (ppStmt ppOff  <$> stmtsNonterm b) <$$>
            ppTermStmt ppOff (stmtsTerm b)) <$$>
  text "}"

ppTermStmt :: ArchConstraints arch
           => (ArchAddrWord arch -> Doc)
              -- ^ Given an address offset, this prints the value
           -> ParsedTermStmt arch ids
           -> Doc
ppTermStmt ppOff tstmt =
  case tstmt of
    ParsedCall s Nothing ->
      text "tail_call" <$$>
      indent 2 (pretty s)
    ParsedCall s (Just next) ->
      text "call and return to" <+> text (show next) <$$>
      indent 2 (pretty s)
    PLTStub regs addr r ->
      text "call_via_got" <+> text (show (relocationSym r)) <+> "(at" <+> text (show addr) PP.<> ")" <$$>
       indent 2 (ppRegMap regs)
    ParsedJump s addr ->
      text "jump" <+> text (show addr) <$$>
      indent 2 (pretty s)
    ParsedLookupTable s idx entries ->
      text "ijump" <+> pretty idx <$$>
      indent 2 (vcat (imap (\i v -> int i <+> text ":->" <+> text (show v))
                           (V.toList entries))) <$$>
      indent 2 (pretty s)
    ParsedReturn s ->
      text "return" <$$>
      indent 2 (pretty s)
    ParsedIte c t f ->
      text "ite" <+> pretty c <$$>
      ppStatementList ppOff t <$$>
      ppStatementList ppOff f
    ParsedArchTermStmt ts s maddr ->
      let addrDoc = case maddr of
                      Just a -> text ", return to" <+> text (show a)
                      Nothing -> text ""
       in prettyF ts <> addrDoc <$$>
          indent 2 (pretty s)
    ParsedTranslateError msg ->
      text "translation error" <+> text (Text.unpack msg)
    ClassifyFailure s ->
      text "unknown transfer" <$$>
      indent 2 (pretty s)

instance ArchConstraints arch => Show (ParsedTermStmt arch ids) where
  show = show . ppTermStmt (text . show)

------------------------------------------------------------------------
-- StatementList

-- | This is a code block after we have classified the control flow
-- statement(s) that the block ends with.
data StatementList arch ids
   = StatementList { stmtsIdent :: !Word64
                     -- ^ An index for uniquely identifying the block.
                     --
                     -- This is primarily used so that we can reference
                     -- which branch lead to a particular next state.
                   , stmtsNonterm :: !([Stmt arch ids])
                     -- ^ The non-terminal statements in the block
                   , stmtsTerm  :: !(ParsedTermStmt arch ids)
                     -- ^ The terminal statement in the block.
                   , stmtsAbsState :: !(AbsProcessorState (ArchReg arch) ids)
                     -- ^ The abstract state of the block just before terminal
                   }

deriving instance ArchConstraints arch
  => Show (StatementList arch ids)

------------------------------------------------------------------------
-- ParsedBlock

-- | A contiguous region of instructions in memory.
data ParsedBlock arch ids
   = ParsedBlock { pblockAddr :: !(ArchSegmentOff arch)
                   -- ^ Address of region
                 , blockSize :: !Int
                   -- ^ The size of the region of memory covered by this.
                 , blockReason :: !(BlockExploreReason (ArchAddrWidth arch))
                   -- ^ Reason that we marked this address as
                   -- the start of a basic block.
                 , blockAbstractState :: !(AbsBlockState (ArchReg arch))
                   -- ^ Abstract state prior to the execution of
                   -- this region.
                 , blockStatementList :: !(StatementList arch ids)
                   -- ^ Returns the entry block for the region
                 }

deriving instance ArchConstraints arch
  => Show (ParsedBlock arch ids)

instance ArchConstraints arch
      => Pretty (ParsedBlock arch ids) where
  pretty b =
    let sl = blockStatementList b
        ppOff o = text (show (incAddr (toInteger o) (segoffAddr (pblockAddr b))))
     in text (show (pblockAddr b)) PP.<> text ":" <$$>
        indent 2 (vcat (ppStmt ppOff <$> stmtsNonterm sl) <$$> ppTermStmt ppOff (stmtsTerm sl))

------------------------------------------------------------------------
-- DiscoveryFunInfo

-- | Information discovered about a particular function
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunReason :: !(FunctionExploreReason (ArchAddrWidth arch))
                      , discoveredFunAddr :: !(ArchSegmentOff arch)
                        -- ^ Address of function entry block.
                      , discoveredFunName :: !BSC.ByteString
                        -- ^ Name of function should be unique for program
                      , _parsedBlocks :: !(Map (ArchSegmentOff arch) (ParsedBlock arch ids))
                        -- ^ Maps an address to the blocks associated with that address.
                      }

parsedBlocks :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentOff arch) (ParsedBlock arch ids))
parsedBlocks = lens _parsedBlocks (\s v -> s { _parsedBlocks = v })

instance ArchConstraints arch => Pretty (DiscoveryFunInfo arch ids) where
  pretty info =
    text "function" <+> text (BSC.unpack (discoveredFunName info))
         <+> "@" <+> pretty (show (discoveredFunAddr info))
    <$$>
    vcat (pretty <$> Map.elems (info^.parsedBlocks))

------------------------------------------------------------------------
-- DiscoveryState

type UnexploredFunctionMap arch =
  Map (ArchSegmentOff arch) (FunctionExploreReason (ArchAddrWidth arch))

-- | Information discovered about the program
data DiscoveryState arch
   = DiscoveryState { memory              :: !(Memory (ArchAddrWidth arch))
                      -- ^ The initial memory when disassembly started.
                    , symbolNames          :: !(AddrSymMap (ArchAddrWidth arch))
                      -- ^ Map addresses to known symbol names
                    , archInfo             :: !(ArchitectureInfo arch)
                      -- ^ Architecture-specific information needed for discovery.
                    , _globalDataMap       :: !(Map (ArchMemAddr arch)
                                                (GlobalDataInfo (ArchMemAddr arch)))
                      -- ^ Maps each address that appears to be global data to information
                      -- inferred about it.
                    , _funInfo             :: !(Map (ArchSegmentOff arch) (Some (DiscoveryFunInfo arch)))
                      -- ^ Map from function addresses to discovered information about function
                    , _unexploredFunctions
                      :: !(UnexploredFunctionMap arch)
                      -- ^ This maps addresses that have been marked as
                      -- functions, but not yet analyzed to the reason
                      -- they are analyzed.
                      --
                      -- The keys in this map and `_funInfo` should be mutually disjoint.
                    , _trustedFunctionEntryPoints :: !(Set (ArchSegmentOff arch))
                      -- ^ This is the set of addresses that we treat
                      -- as definitely belonging to function entry
                      -- points.
                      --
                      -- The discovery process will not allow
                      -- intra-procedural jumps to these addresses.
                      -- Jumps to these addresses must either be calls
                      -- or tail calls.
                      --
                      -- To ensure translation is invariant on the
                      -- order in which functions are visited, this
                      -- set should be initialized upfront, and not
                      -- changed.
                    , _exploreFnPred :: Maybe (ArchSegmentOff arch -> Bool)
                      -- ^ if present, this predicate decides whether to explore
                      -- a function at the given address or not
                    }

-- | Return list of all functions discovered so far.
exploredFunctions :: DiscoveryState arch -> [Some (DiscoveryFunInfo arch)]
exploredFunctions i = Map.elems $ i^.funInfo

withDiscoveryArchConstraints :: DiscoveryState arch
                             -> (ArchConstraints arch => a)
                             -> a
withDiscoveryArchConstraints dinfo = withArchConstraints (archInfo dinfo)

ppDiscoveryStateBlocks :: DiscoveryState arch
                      -> Doc
ppDiscoveryStateBlocks info = withDiscoveryArchConstraints info $
    vcat $ f <$> Map.elems (info^.funInfo)
  where f :: ArchConstraints arch => Some (DiscoveryFunInfo arch) -> Doc
        f (Some v) = pretty v

-- | Create empty discovery information.
emptyDiscoveryState :: Memory (ArchAddrWidth arch)
                       -- ^ State of memory
                    -> AddrSymMap (ArchAddrWidth arch)
                       -- ^ Map from addresses to their symbol name (if any)
                    -> ArchitectureInfo arch
                       -- ^ architecture/OS specific information
                    -> DiscoveryState arch
emptyDiscoveryState mem addrSymMap info =
  DiscoveryState
  { memory               = mem
  , symbolNames          = addrSymMap
  , archInfo             = info
  , _globalDataMap       = Map.empty
  , _funInfo             = Map.empty
  , _unexploredFunctions = Map.empty
  , _trustedFunctionEntryPoints = Map.keysSet addrSymMap
  , _exploreFnPred       = Nothing
  }

-- | Map each jump table start to the address just after the end.
globalDataMap
  :: Simple Lens (DiscoveryState arch) (Map (ArchMemAddr arch) (GlobalDataInfo (ArchMemAddr arch)))
globalDataMap = lens _globalDataMap (\s v -> s { _globalDataMap = v })

-- | List of functions to explore next.
unexploredFunctions
  :: Simple Lens (DiscoveryState arch) (UnexploredFunctionMap arch)
unexploredFunctions = lens _unexploredFunctions (\s v -> s { _unexploredFunctions = v })

-- | Get information for specific functions
funInfo :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentOff arch) (Some (DiscoveryFunInfo arch)))
funInfo = lens _funInfo (\s v -> s { _funInfo = v })

trustedFunctionEntryPoints :: Simple Lens (DiscoveryState arch) (Set (ArchSegmentOff arch))
trustedFunctionEntryPoints =
  lens _trustedFunctionEntryPoints
       (\s v -> s { _trustedFunctionEntryPoints = v })

exploreFnPred :: Simple Lens (DiscoveryState arch) (Maybe (ArchSegmentOff arch -> Bool))
exploreFnPred = lens _exploreFnPred (\s v -> s { _exploreFnPred = v })

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Constraint on architecture register values needed by code exploration.
type RegConstraint r = (OrdF r, HasRepr r TypeRepr, RegisterInfo r, ShowF r)
