{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : Test.DejaFu.Heap
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses
--
-- A heterogeneous type-safe map.
module Test.DejaFu.Heap where

import           Control.Monad.ST   (ST)
import           Data.Maybe         (fromMaybe)
import qualified Data.Vault.Lazy    as VIO
import qualified Data.Vault.ST.Lazy as VST

-- avoid overlapping
newtype IOHeap     = IOHeap  VIO.Vault
newtype IOKey    a = IOKey  (VIO.Key     a)
newtype STHeap s   = STHeap (VST.Vault s)
newtype STKey  s a = STKey  (VST.Key   s a)

-- | A heterogeneous type-safe map.
--
-- @since unreleased
class Monad monad => Heap heap key monad | heap -> monad, heap -> key, monad -> heap, key -> heap where
  -- | The empty heap
  empty :: heap

  -- | Insert a value, producing a new key.
  insert :: a -> heap -> monad (key a, heap)

  -- | Look up a value by key.  Throws an error if the key is not
  -- valid, as there is no way to delete keys, this can only happen if
  -- keys from one heap are used in another.
  lookup :: key a -> heap -> a

  -- | Overwrite a value.
  set :: key a -> a -> heap -> heap

instance Heap IOHeap IOKey IO where
  empty = IOHeap VIO.empty

  insert a (IOHeap v) = do
    k <- VIO.newKey
    pure (IOKey k, IOHeap (VIO.insert k a v))

  lookup (IOKey k) (IOHeap v) =
    fromMaybe (error "somehow you got an invalid key") (VIO.lookup k v)

  set (IOKey k) a (IOHeap v) =
    IOHeap (VIO.insert k a v)

instance Heap (STHeap s) (STKey s) (ST s) where
  empty = STHeap VST.empty

  insert a (STHeap v) = do
    k <- VST.newKey
    pure (STKey k, STHeap (VST.insert k a v))

  lookup (STKey k) (STHeap v) =
    fromMaybe (error "somehow you got an invalid key") (VST.lookup k v)

  set (STKey k) a (STHeap v) =
    STHeap (VST.insert k a v)
