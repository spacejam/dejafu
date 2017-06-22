{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Test.DejaFu.STM
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : FlexibleContexts, GeneralizedNewtypeDeriving, RankNTypes, TypeFamilies
--
-- A 'MonadSTM' implementation, which can be run on top of 'IO' or
-- 'ST'.
module Test.DejaFu.STM
  ( -- * The @STMLike@ Monad
    STMLike
  , STMST
  , STMIO

  -- * Executing Transactions
  , Result(..)
  , TTrace
  , TAction(..)
  , TVarId
  , runTransaction
  ) where

import           Control.Monad.Catch      (MonadCatch(..), MonadThrow(..))
import           Control.Monad.Cont       (cont)
import           Control.Monad.Ref        (MonadRef)

import qualified Control.Monad.STM.Class  as C
import           Test.DejaFu.Common
import qualified Test.DejaFu.Heap         as H
import           Test.DejaFu.STM.Internal

-- | @since unreleased
newtype STMLike heap key monad a = S { runSTM :: M heap key monad a } deriving (Functor, Applicative, Monad)

-- | Create a new STM continuation.
toSTM :: ((a -> STMAction heap key monad) -> STMAction heap key monad) -> STMLike heap key monad a
toSTM = S . cont

-- | A 'MonadSTM' implementation using @ST@, it encapsulates a single
-- atomic transaction. The environment, that is, the collection of
-- defined 'TVar's is implicit, there is no list of them, they exist
-- purely as references. This makes the types simpler, but means you
-- can't really get an aggregate of them (if you ever wanted to for
-- some reason).
--
-- @since 0.3.0.0
type STMST t = STMLike (H.STHeap t)

-- | A 'MonadSTM' implementation using @ST@, it encapsulates a single
-- atomic transaction. The environment, that is, the collection of
-- defined 'TVar's is implicit, there is no list of them, they exist
-- purely as references. This makes the types simpler, but means you
-- can't really get an aggregate of them (if you ever wanted to for
-- some reason).
--
-- @since 0.3.0.0
type STMIO = STMLike H.IOHeap

instance MonadThrow (STMLike heap key monad) where
  throwM = toSTM . const . SThrow

instance MonadCatch (STMLike heap key monad) where
  catch (S stm) handler = toSTM (SCatch (runSTM . handler) stm)

instance C.MonadSTM (STMLike heap key monad) where
  type TVar (STMLike heap key monad) = TVar key

  retry = toSTM (const SRetry)

  orElse (S a) (S b) = toSTM (SOrElse a b)

  newTVarN n = toSTM . SNew n

  readTVar = toSTM . SRead

  writeTVar tvar a = toSTM (\c -> SWrite tvar a (c ()))

-- | Run a transaction, returning the result and new initial
-- 'TVarId'. If the transaction ended by calling 'retry', any 'TVar'
-- modifications are undone.
--
-- @since unreleased
runTransaction :: (H.Heap heap key monad, MonadRef r monad)
  => STMLike heap key monad a
  -> IdSource
  -> heap
  -> monad (heap, Result a, IdSource, TTrace)
runTransaction ma tvid heap = do
  (res, heap', tvid', trace) <- doTransaction heap (runSTM ma) tvid
  pure (if isSTMSuccess res then heap' else heap, res, tvid', trace)
