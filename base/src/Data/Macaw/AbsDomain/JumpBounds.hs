{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Macaw.AbsDomain.JumpBounds
  ( InitialIndexBounds
  , arbitraryInitialBounds
  , joinInitialBounds
  , IndexBounds
  , mkIndexBounds
  , UpperBound(..)
  , addUpperBound
  , assertPred
  , unsignedUpperBound
  , nextBlockBounds
  ) where

import           Control.Lens
import           Control.Monad.State
import           Data.Bits
import           Data.Functor
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr (maxUnsigned)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.CFG
import           Data.Macaw.Types

-- | An upper bound on a value.
data UpperBound tp
   = forall w . (tp ~ BVType w) => IntegerUpperBound Integer

instance Eq (UpperBound tp) where
  IntegerUpperBound x == IntegerUpperBound y = x == y

instance MapF.EqF UpperBound where
  eqF = (==)

instance Ord (UpperBound tp) where
  compare (IntegerUpperBound x) (IntegerUpperBound y) = compare x y

deriving instance Show (UpperBound tp)

-- | Bounds for a function as the start of a block.
data InitialIndexBounds r
   = InitialIndexBounds { initialRegUpperBound :: !(MapF r UpperBound)
                        }

instance MapF.TestEquality r => Eq (InitialIndexBounds r) where
   x == y = initialRegUpperBound x == initialRegUpperBound y

instance ShowF r => Pretty (InitialIndexBounds r) where
  pretty r = vcat $ ppPair <$> MapF.toList (initialRegUpperBound r)
    where ppPair :: MapF.Pair r UpperBound -> Doc
          ppPair (MapF.Pair k (IntegerUpperBound b)) = text (showF k) <+> text "<=" <+> text (show b)

-- | Create initial index bounds that can represent any system state.
arbitraryInitialBounds :: InitialIndexBounds reg
arbitraryInitialBounds = InitialIndexBounds { initialRegUpperBound = MapF.empty }


type Changed = State Bool

markChanged :: Bool -> Changed ()
markChanged b = modify (|| b)

runChanged :: Changed a -> Maybe a
runChanged action =
  case runState action False of
    (r, True)  -> Just r
    (_, False) -> Nothing

-- | Take the union of two index bounds
joinInitialBounds :: forall r
                  .  MapF.OrdF r
                  => InitialIndexBounds r
                  -> InitialIndexBounds r
                  -> Maybe (InitialIndexBounds r)
joinInitialBounds old new = runChanged $ do
  let combineF :: r tp -> UpperBound tp -> UpperBound tp -> Changed (Maybe (UpperBound tp))
      combineF _ (IntegerUpperBound x) (IntegerUpperBound y) =
        markChanged (x < y) $> Just (IntegerUpperBound (max x y))

      -- Mark upper bounds exclusively in old set.
      -- If we have any only-old bounds add mark value as changed.
      oldF :: MapF r UpperBound -> Changed (MapF r UpperBound)
      oldF m = markChanged (not (MapF.null m)) $> MapF.empty

      -- How to upper bounds exclusively in new set.
      -- Drop any only-new bounds.
      newF :: MapF r UpperBound -> Changed (MapF r UpperBound)
      newF _ = pure MapF.empty

  z <- MapF.mergeWithKeyM combineF oldF newF (initialRegUpperBound old) (initialRegUpperBound new)
  pure InitialIndexBounds { initialRegUpperBound = z }

-- | Maintains upper bound information on values within a block.
--
-- This is used exclusively for inferring upper bounds of jump table
-- indices, and is not intended to be a complete decision procedure.
-- The results are sound in that when `unsignedUpperBound` returns an
-- upper bound then that is indeed an upper bound implied by past
-- assertions, and when `assertPred` returns an inconsistency, then
-- the assertions do indeed not have a model.
data IndexBounds reg ids
   = IndexBounds { _regBounds :: !(MapF reg UpperBound)
                 , _assignUpperBound :: !(MapF (AssignId ids) UpperBound)
                 }

-- | Maps assignment ids to the associated upper bounds
regBounds :: Simple Lens (IndexBounds reg ids) (MapF reg UpperBound)
regBounds = lens _regBounds (\s v -> s { _regBounds = v })

-- | Maps assignment ids to the associated upper bounds
assignUpperBound :: Simple Lens (IndexBounds reg ids) (MapF (AssignId ids) UpperBound)
assignUpperBound = lens _assignUpperBound (\s v -> s { _assignUpperBound = v })

-- | Create index bounds from initial index bounds.
mkIndexBounds :: InitialIndexBounds reg -> IndexBounds reg ids
mkIndexBounds i = IndexBounds { _regBounds = initialRegUpperBound i
                              , _assignUpperBound = MapF.empty
                              }

-- | `addUpperBound v u bnds` adds an assertion `v <= u` (where <= is unsigned)
-- to the list of bounds maintained, and returns the new bounds or `Nothing` if
-- bounds are now inconsistent.
addUpperBound :: ( MapF.OrdF (ArchReg arch)
                 , HasRepr (ArchReg arch) TypeRepr
                 )
               => BVValue arch ids w -- ^ to bound
               -> Integer -- ^ Upper bound as an unsigned number
               -> IndexBounds (ArchReg arch) ids
               -> Maybe (IndexBounds (ArchReg arch) ids)
addUpperBound v u bnds
    -- Do nothing if upper bounds equals or exceeds the maximum value it could be.
  | u >= maxUnsigned (typeWidth v) = Just bnds
  | u < 0 = error "addUpperBound given negative value."
  | otherwise =
  case v of
    BVValue _ c | c <= u -> Just bnds
                | otherwise -> Nothing
    -- Skip these
    RelocatableValue{} -> Just bnds
    -- Skip these
    SymbolValue{}      -> Just bnds
    -- Do nothing for this
    ThisFunctionAddr{} -> Just bnds
    AssignedValue a ->
      case assignRhs a of
        EvalApp (UExt x _) -> addUpperBound x u bnds
        EvalApp (Trunc x w) ->
          -- TODO: This is unsound -- we need to fix it.
          if u < maxUnsigned w then
            addUpperBound x u bnds
           else
            Just $ bnds
        _ ->
          Just $! (bnds & assignUpperBound %~ MapF.insertWith min (assignId a) (IntegerUpperBound u))
    Initial r ->
      Just $! (bnds & regBounds %~ MapF.insertWith min r (IntegerUpperBound u))

-- | Assert a predicate is either `True` or `False` and either return updated bounds, or
-- return `Nothing` if bounds are now inconsistent.
assertPred :: ( OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              )
           => Value arch ids BoolType -- ^ Value represnting predicate
           -> Bool -- ^ Controls whether predicate is true or false
           -> IndexBounds (ArchReg arch) ids -- ^ Current index bounds
           -> Maybe (IndexBounds (ArchReg arch) ids)
assertPred (AssignedValue a) isTrue bnds =
  case assignRhs a of
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c)) | isTrue     -> addUpperBound x (c-1) bnds
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue _ c) y) | not isTrue -> addUpperBound y c bnds
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue _ c)) | isTrue     -> addUpperBound x c bnds
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y) | not isTrue -> addUpperBound y (c-1) bnds
    -- Given x && y, assert x, then assert y
    EvalApp (AndApp l r) | isTrue     -> assertPred l True  bnds >>= assertPred r True
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) | not isTrue -> assertPred l False bnds >>= assertPred r False
    EvalApp (NotApp p) -> assertPred p (not isTrue) bnds
    _ -> Just bnds
assertPred _ _ bnds = Just bnds

-- | Lookup an upper bound or return analysis for why it is not defined.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                  => IndexBounds (ArchReg arch) ids
                  -> Value arch ids (BVType w)
                  -> Either String (UpperBound (BVType w))
unsignedUpperBound bnds v =
  case v of
    BVValue _ i -> Right (IntegerUpperBound i)
    RelocatableValue{} ->
      Left "Relocatable values do not have bounds."
    SymbolValue{} ->
      Left "Symbol values do not have bounds."
    ThisFunctionAddr{} ->
      Left "This function addr does not have bounds."
    AssignedValue a ->
      case MapF.lookup (assignId a) (bnds^.assignUpperBound) of
        Just bnd -> Right bnd
        Nothing ->
          case assignRhs a of
            EvalApp (BVAnd _ x y) -> do
              case (unsignedUpperBound bnds x,  unsignedUpperBound bnds y) of
                (Right (IntegerUpperBound xb), Right (IntegerUpperBound yb)) ->
                  Right (IntegerUpperBound (min xb yb))
                (Right xb, Left{}) -> Right xb
                (Left{}, yb)       -> yb
            EvalApp (SExt x w) -> do
              IntegerUpperBound r <- unsignedUpperBound bnds x
              -- sign-extend r
              pure . IntegerUpperBound
                $ if r < 2^(natValue w-1)
                  then r
                  else maxUnsigned (typeWidth v) .&. r
            EvalApp (UExt x _) -> do
              IntegerUpperBound r <- unsignedUpperBound bnds x
              pure (IntegerUpperBound r)
            EvalApp (Trunc x w) -> do
              IntegerUpperBound xr <- unsignedUpperBound bnds x
              pure $! IntegerUpperBound (min xr (maxUnsigned w))
            _ -> Left $ "Could not find upper bounds for " ++ show (assignId a) ++ "."
    Initial r ->
      case MapF.lookup r (bnds^.regBounds) of
        Just bnd -> Right bnd
        Nothing -> Left $ "No upper bounds for " ++ showF r ++ "."

eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Right v) = Just v
eitherToMaybe Left{}    = Nothing


nextBlockBounds :: forall arch ids
                .  ( MapF.OrdF (ArchReg arch)
                   , MapF.ShowF (ArchReg arch)
                   , RegisterInfo (ArchReg arch)
                   )
                => IndexBounds (ArchReg arch) ids
                   -- ^ Index bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitialIndexBounds (ArchReg arch)
nextBlockBounds bnds regs =
  let m = regStateMap regs
      f :: Value arch ids tp -> Maybe (UpperBound tp)
      f v =
        case typeRepr v of
          BoolTypeRepr -> Nothing
          BVTypeRepr _ -> eitherToMaybe (unsignedUpperBound bnds v)
          TupleTypeRepr{} -> Nothing
   in InitialIndexBounds { initialRegUpperBound = MapF.mapMaybe f m
                         }
