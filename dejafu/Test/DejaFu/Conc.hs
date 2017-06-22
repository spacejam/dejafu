{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Test.DejaFu.Conc
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TypeFamilies, TypeSynonymInstances, UndecidableInstances
--
-- Deterministic traced execution of concurrent computations.
--
-- This works by executing the computation on a single thread, calling
-- out to the supplied scheduler after each step to determine which
-- thread runs next.
module Test.DejaFu.Conc
  ( -- * The @Conc@ monad
    Conc
  , ConcST
  , ConcIO

  -- * Executing computations
  , Failure(..)
  , MemType(..)
  , runConcurrent
  , subconcurrency

  -- * Execution traces
  , Trace
  , Decision(..)
  , ThreadId(..)
  , ThreadAction(..)
  , Lookahead(..)
  , MVarId
  , CRefId
  , MaskingState(..)
  , showTrace
  , showFail

  -- * Scheduling
  , module Test.DejaFu.Schedule
  ) where

import           Control.Exception                (MaskingState(..))
import qualified Control.Monad.Base               as Ba
import qualified Control.Monad.Catch              as Ca
import qualified Control.Monad.IO.Class           as IO
import           Control.Monad.Ref                (MonadRef)
import qualified Control.Monad.Ref                as Re
import           Control.Monad.ST                 (ST)
import qualified Data.Foldable                    as F
import           Test.DejaFu.Schedule

import qualified Control.Monad.Conc.Class         as C
import           Test.DejaFu.Common
import           Test.DejaFu.Conc.Internal
import           Test.DejaFu.Conc.Internal.Common
import qualified Test.DejaFu.Heap                 as H
import           Test.DejaFu.STM

-- | @since unreleased
newtype Conc heap key monad a = C { unC :: M heap key monad a } deriving (Functor, Applicative, Monad)

-- | A 'MonadConc' implementation using @ST@, this should be preferred
-- if you do not need 'liftIO'.
--
-- @since 0.4.0.0
type ConcST t = Conc (H.STHeap t) (H.STKey t) (ST t)

-- | A 'MonadConc' implementation using @IO@.
--
-- @since 0.4.0.0
type ConcIO = Conc H.IOHeap H.IOKey IO

toConc :: ((a -> Action heap key monad) -> Action heap key monad) -> Conc heap key monad a
toConc = C . cont

wrap :: (M heap key monad a -> M heap key monad a) -> Conc heap key monad a -> Conc heap key monad a
wrap f = C . f . unC

instance IO.MonadIO ConcIO where
  liftIO ma = toConc (\c -> ALift (fmap c ma))

instance Ba.MonadBase IO ConcIO where
  liftBase = IO.liftIO

instance Re.MonadRef (CRef key) (Conc heap key monad) where
  newRef a = toConc (ANewCRef "" a)

  readRef ref = toConc (AReadCRef ref)

  writeRef ref a = toConc (\c -> AWriteCRef ref a (c ()))

  modifyRef ref f = toConc (AModCRef ref (\a -> (f a, ())))

instance Re.MonadAtomicRef (CRef key) (Conc heap key monad) where
  atomicModifyRef ref f = toConc (AModCRef ref f)

instance Ca.MonadCatch (Conc heap key monad) where
  catch ma h = toConc (ACatching (unC . h) (unC ma))

instance Ca.MonadThrow (Conc heap key monad) where
  throwM e = toConc (\_ -> AThrow e)

instance Ca.MonadMask (Conc heap key monad) where
  mask                mb = toConc (AMasking MaskedInterruptible   (\f -> unC $ mb $ wrap f))
  uninterruptibleMask mb = toConc (AMasking MaskedUninterruptible (\f -> unC $ mb $ wrap f))

instance H.Heap heap key monad => C.MonadConc (Conc heap key monad) where
  type MVar     (Conc heap key monad) = MVar key
  type CRef     (Conc heap key monad) = CRef key
  type Ticket   (Conc heap key monad) = Ticket
  type STM      (Conc heap key monad) = STMLike heap key monad
  type ThreadId (Conc heap key monad) = ThreadId

  -- ----------

  forkWithUnmaskN   n ma = toConc (AFork n (\umask -> runCont (unC $ ma $ wrap umask) (\_ -> AStop (pure ()))))
  forkOnWithUnmaskN n _  = C.forkWithUnmaskN n

  -- This implementation lies and returns 2 until a value is set. This
  -- will potentially avoid special-case behaviour for 1 capability,
  -- so it seems a sane choice.
  getNumCapabilities      = toConc AGetNumCapabilities
  setNumCapabilities caps = toConc (\c -> ASetNumCapabilities caps (c ()))

  myThreadId = toConc AMyTId

  yield = toConc (\c -> AYield (c ()))

  -- ----------

  newCRefN n a = toConc (ANewCRef n a)

  readCRef   ref = toConc (AReadCRef    ref)
  readForCAS ref = toConc (AReadCRefCas ref)

  peekTicket' _ = _ticketVal

  writeCRef ref      a = toConc (\c -> AWriteCRef ref a (c ()))
  casCRef   ref tick a = toConc (ACasCRef ref tick a)

  atomicModifyCRef ref f = toConc (AModCRef    ref f)
  modifyCRefCAS    ref f = toConc (AModCRefCas ref f)

  -- ----------

  newEmptyMVarN n = toConc (ANewMVar n)

  putMVar  var a = toConc (\c -> APutMVar var a (c ()))
  readMVar var   = toConc (AReadMVar var)
  takeMVar var   = toConc (ATakeMVar var)

  tryPutMVar  var a = toConc (ATryPutMVar  var a)
  tryReadMVar var   = toConc (ATryReadMVar var)
  tryTakeMVar var   = toConc (ATryTakeMVar var)

  -- ----------

  throwTo tid e = toConc (\c -> AThrowTo tid e (c ()))

  -- ----------

  atomically = toConc . AAtom

-- | Run a concurrent computation with a given 'Scheduler' and initial
-- state, returning a failure reason on error. Also returned is the
-- final state of the scheduler, and an execution trace.
--
-- __Warning:__ Blocking on the action of another thread in 'liftIO'
-- cannot be detected! So if you perform some potentially blocking
-- action in a 'liftIO' the entire collection of threads may deadlock!
-- You should therefore keep @IO@ blocks small, and only perform
-- blocking operations with the supplied primitives, insofar as
-- possible.
--
-- __Note:__ In order to prevent computation from hanging, the runtime
-- will assume that a deadlock situation has arisen if the scheduler
-- attempts to (a) schedule a blocked thread, or (b) schedule a
-- nonexistent thread. In either of those cases, the computation will
-- be halted.
--
-- @since unreleased
runConcurrent :: (H.Heap heap key monad, MonadRef r monad)
  => Scheduler s
  -> MemType
  -> s
  -> Conc heap key monad a
  -> monad (Either Failure a, s, Trace)
runConcurrent sched memtype s ma = do
  (res, ctx, trace, _) <- runConcurrency sched memtype s initialIdSource 2 H.empty (unC ma)
  pure (res, cSchedState ctx, F.toList trace)

-- | Run a concurrent computation and return its result.
--
-- This can only be called in the main thread, when no other threads
-- exist. Calls to 'subconcurrency' cannot be nested. Violating either
-- of these conditions will result in the computation failing with
-- @IllegalSubconcurrency@.
--
-- @since 0.6.0.0
subconcurrency :: Conc heap key monad a -> Conc heap key monad (Either Failure a)
subconcurrency ma = toConc (ASub (unC ma))
