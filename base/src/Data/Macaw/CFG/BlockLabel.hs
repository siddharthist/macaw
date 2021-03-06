{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines a pair for referencing a block within a function.
-}
module Data.Macaw.CFG.BlockLabel
  ( BlockLabel(..)
  , isRootBlockLabel
  , rootBlockLabel
  , mkRootBlockLabel
  , ArchLabel
  ) where

import qualified Data.Monoid as Monoid
import           Data.Word
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.CFG
import           Data.Macaw.Memory (MemWidth(..), MemSegmentOff)

-- | A label used to identify a block within a function.
--
-- The field is the address width.
data BlockLabel w
   = GeneratedBlock { labelAddr   :: !(MemSegmentOff w)
                      -- ^ Address of function label
                    , labelIndex  :: {-# UNPACK #-} !Word64
                    -- ^ A unique identifier for a generated block.
                    }
  deriving Eq

isRootBlockLabel :: BlockLabel w -> Bool
isRootBlockLabel (GeneratedBlock _ w) = w == 0

rootBlockLabel :: BlockLabel w -> BlockLabel w
rootBlockLabel (GeneratedBlock p _) = GeneratedBlock p 0

mkRootBlockLabel :: MemSegmentOff w -> BlockLabel w
mkRootBlockLabel p = GeneratedBlock p 0

instance Ord (BlockLabel w) where
  compare (GeneratedBlock p v) (GeneratedBlock p' v') =
    compare p p' Monoid.<> compare v v'

instance MemWidth w => Show (BlockLabel w) where
  showsPrec _ (GeneratedBlock a 0) s = "block_" ++ shows a s
  showsPrec _ (GeneratedBlock a w) s = "subblock_" ++ shows a ("_" ++ shows w s)
  {-# INLINABLE showsPrec #-}

instance MemWidth w => Pretty (BlockLabel w) where
  pretty l = text (show l)

type ArchLabel arch = BlockLabel (ArchAddrWidth arch)
