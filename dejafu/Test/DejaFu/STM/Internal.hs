{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : Test.DejaFu.STM.Internal
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ExistentialQuantification, FlexibleContexts, MultiParamTypeClasses
--
-- 'MonadSTM' testing implementation, internal types and
-- definitions. This module is NOT considered to form part of the
-- public interface of this library.
module Test.DejaFu.STM.Internal where

import           Control.DeepSeq    (NFData(..))
import           Control.Exception  (Exception, SomeException, fromException,
                                     toException)
import           Control.Monad.Cont (Cont, runCont)
import           Control.Monad.Ref  (MonadRef, readRef, writeRef)
import           Data.List          (nub)

import           Test.DejaFu.Common
import qualified Test.DejaFu.Heap   as H

--------------------------------------------------------------------------------
-- The @STMLike@ monad

-- | The underlying monad is based on continuations over primitive
-- actions.
type M heap key monad a = Cont (STMAction heap key monad) a

--------------------------------------------------------------------------------
-- * Primitive actions

-- | STM transactions are represented as a sequence of primitive
-- actions.
data STMAction heap key monad
  = forall a e. Exception e => SCatch (e -> M heap key monad a) (M heap key monad a) (a -> STMAction heap key monad)
  | forall a. SRead  (TVar key a) (a -> STMAction heap key monad)
  | forall a. SWrite (TVar key a) a (STMAction heap key monad)
  | forall a. SOrElse (M heap key monad a) (M heap key monad a) (a -> STMAction heap key monad)
  | forall a. SNew String a (TVar key a -> STMAction heap key monad)
  | forall e. Exception e => SThrow e
  | SRetry
  | SStop (monad ())

--------------------------------------------------------------------------------
-- * @TVar@s

-- | A 'TVar' is a tuple of a unique ID and the value contained. The
-- ID is so that blocked transactions can be re-run when a 'TVar' they
-- depend on has changed.
newtype TVar key a = TVar (TVarId, key a)

--------------------------------------------------------------------------------
-- * Output

-- | The result of an STM transaction, along with which 'TVar's it
-- touched whilst executing.
--
-- @since 0.1.0.0
data Result a =
    Success [TVarId] [TVarId] a
  -- ^ The transaction completed successfully, reading the first list
  -- 'TVar's and writing to the second.
  | Retry [TVarId]
  -- ^ The transaction aborted by calling 'retry', and read the
  -- returned 'TVar's. It should be retried when at least one of the
  -- 'TVar's has been mutated.
  | Exception SomeException
  -- ^ The transaction aborted by throwing an exception.
  deriving Show

-- | This only reduces a 'SomeException' to WHNF.
--
-- @since 0.5.1.0
instance NFData a => NFData (Result a) where
  rnf (Success tr1 tr2 a) = rnf (tr1, tr2, a)
  rnf (Retry tr) = rnf tr
  rnf (Exception e) = e `seq` ()

-- | Check if a 'Result' is a @Success@.
isSTMSuccess :: Result a -> Bool
isSTMSuccess (Success _ _ _) = True
isSTMSuccess _ = False

instance Functor Result where
  fmap f (Success rs ws a) = Success rs ws $ f a
  fmap _ (Retry rs)    = Retry rs
  fmap _ (Exception e) = Exception e

instance Foldable Result where
  foldMap f (Success _ _ a) = f a
  foldMap _ _ = mempty

--------------------------------------------------------------------------------
-- * Execution

-- | Run a STM transaction.
doTransaction :: (H.Heap heap key monad, MonadRef r monad)
  => heap -> M heap key monad a -> IdSource -> monad (Result a, heap, IdSource, TTrace)
doTransaction heap0 ma idsource = do
  (c, ref) <- runRefCont SStop (Just . Right) (runCont ma)
  (idsource', heap', readen, written, trace) <- go ref c heap0 idsource [] [] []
  res <- readRef ref

  case res of
    Just (Right val) -> pure (Success (nub readen) (nub written) val, heap', idsource', reverse trace)
    Just (Left  exc) -> pure (Exception exc,      heap0, idsource, reverse trace)
    Nothing          -> pure (Retry $ nub readen, heap0, idsource, reverse trace)

  where
    go ref act heap nidsrc readen written sofar = do
      (act', heap', nidsrc', readen', written', tact) <- stepTrans heap act nidsrc

      let newIDSource = nidsrc'
          newAct = act'
          newReaden = readen' ++ readen
          newWritten = written' ++ written
          newSofar = tact : sofar

      case tact of
        TStop  -> pure (newIDSource, heap', newReaden, newWritten, TStop:newSofar)
        TRetry -> do
          writeRef ref Nothing
          pure (newIDSource, heap', newReaden, newWritten, TRetry:newSofar)
        TThrow -> do
          writeRef ref (Just . Left $ case act of SThrow e -> toException e; _ -> undefined)
          pure (newIDSource, heap', newReaden, newWritten, TThrow:newSofar)
        _ -> go ref newAct heap' newIDSource newReaden newWritten newSofar

-- | Run a transaction for one step.
stepTrans :: (H.Heap heap key monad, MonadRef r monad)
  => heap -> STMAction heap key monad -> IdSource -> monad (STMAction heap key monad, heap, IdSource, [TVarId], [TVarId], TAction)
stepTrans heap act idsource = case act of
  SCatch  h stm c -> stepCatch h stm c
  SRead   ref c   -> stepRead ref c
  SWrite  ref a c -> stepWrite ref a c
  SNew    n a c   -> stepNew n a c
  SOrElse a b c   -> stepOrElse a b c
  SStop   na      -> stepStop na

  SThrow e -> pure (SThrow e, heap, idsource, [], [], TThrow)
  SRetry   -> pure (SRetry,   heap, idsource, [], [], TRetry)

  where
    stepCatch h stm c = cases TCatch stm c
      (\trace -> pure (SRetry, heap, idsource, [], [], TCatch trace Nothing))
      (\trace exc    -> case fromException exc of
        Just exc' -> transaction (TCatch trace . Just) (h exc') c
        Nothing   -> pure (SThrow exc, heap, idsource, [], [], TCatch trace Nothing))

    stepRead (TVar (tvid, k)) c =
      let val = H.lookup k heap
      in pure (c val, heap, idsource, [tvid], [], TRead tvid)

    stepWrite (TVar (tvid, k)) a c =
      let heap' = H.set k a heap
      in pure (c, heap', idsource, [], [tvid], TWrite tvid)

    stepNew n a c = do
      let (idsource', tvid) = nextTVId n idsource
      (key, heap') <- H.insert a heap
      let tvar = TVar (tvid, key)
      pure (c tvar, heap', idsource', [], [tvid], TNew)

    stepOrElse a b c = cases TOrElse a c
      (\trace   -> transaction (TOrElse trace . Just) b c)
      (\trace exc -> pure (SThrow exc, heap, idsource, [], [], TOrElse trace Nothing))

    stepStop na = do
      na
      pure (SStop na, heap, idsource, [], [], TStop)

    cases tact stm onSuccess onRetry onException = do
      (res, heap', idsource', trace) <- doTransaction heap stm idsource
      case res of
        Success readen written val -> pure (onSuccess val, heap', idsource', readen, written, tact trace Nothing)
        Retry readen -> do
          (res', heap'', idsource'', readen', written', trace') <- onRetry trace
          pure (res', heap'', idsource'', readen ++ readen', written', trace')
        Exception exc -> onException trace exc

    transaction tact stm onSuccess = cases (\t _ -> tact t) stm onSuccess
      (\trace     -> pure (SRetry,     heap, idsource, [], [], tact trace))
      (\trace exc -> pure (SThrow exc, heap, idsource, [], [], tact trace))
