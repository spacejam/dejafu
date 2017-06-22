{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : Test.DejaFu.Conc.Internal.Common
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ExistentialQuantification, RankNTypes
--
-- Common types and utility functions for deterministic execution of
-- 'MonadConc' implementations. This module is NOT considered to form
module Test.DejaFu.Conc.Internal.Common where

import           Control.Exception  (Exception, MaskingState(..))
import           Data.List.NonEmpty (NonEmpty, fromList)
import           Data.Map.Strict    (Map)
import           Test.DejaFu.Common
import           Test.DejaFu.STM    (STMLike)

--------------------------------------------------------------------------------
-- * The @Conc@ Monad

-- | The underlying monad is based on continuations over 'Action's.
--
-- One might wonder why the return type isn't reflected in 'Action',
-- and a free monad formulation used. This would remove the need for a
-- @AStop@ actions having their parameter. However, this makes the
-- current expression of threads and exception handlers very difficult
-- (perhaps even not possible without significant reworking), so I
-- abandoned the attempt.
newtype M heap key monad a = M { runM :: (a -> Action heap key monad) -> Action heap key monad }

instance Functor (M heap key monad) where
    fmap f m = M $ \ c -> runM m (c . f)

instance Applicative (M heap key monad) where
    pure x  = M $ \c -> AReturn $ c x
    f <*> v = M $ \c -> runM f (\g -> runM v (c . g))

instance Monad (M heap key monad) where
    return  = pure
    m >>= k = M $ \c -> runM m (\x -> runM (k x) c)

-- | The concurrent variable type used with the 'Conc' monad. One
-- notable difference between these and 'MVar's is that 'MVar's are
-- single-wakeup, and wake up in a FIFO order. Writing to a @MVar@
-- wakes up all threads blocked on reading it, and it is up to the
-- scheduler which one runs next. Taking from a @MVar@ behaves
-- analogously.
data MVar key a = MVar
  { _cvarId   :: MVarId
  , _cvarVal  :: key (Maybe a)
  }

-- | The mutable non-blocking reference type. These are like 'IORef's.
--
-- @CRef@s are represented as a unique numeric identifier and a
-- reference containing (a) any thread-local non-synchronised writes
-- (so each thread sees its latest write), (b) a commit count (used in
-- compare-and-swaps), and (c) the current value visible to all
-- threads.
data CRef key a = CRef
  { _crefId   :: CRefId
  , _crefVal  :: key (Map ThreadId (a, Integer), Integer, a)
  }

-- | The compare-and-swap proof type.
--
-- @Ticket@s are represented as just a wrapper around the identifier
-- of the 'CRef' it came from, the commit count at the time it was
-- produced, and an @a@ value. This doesn't work in the source package
-- (atomic-primops) because of the need to use pointer equality. Here
-- we can just pack extra information into 'CRef' to avoid that need.
data Ticket a = Ticket
  { _ticketCRef     :: CRefId
  , _ticketWrites   :: Integer
  , _ticketMyWrites :: Integer
  , _ticketVal      :: a
  }

-- | Construct a continuation-passing operation from a function.
cont :: ((a -> Action heap key monad) -> Action heap key monad) -> M heap key monad a
cont = M

-- | Run a CPS computation with the given final computation.
runCont :: M heap key monad a -> (a -> Action heap key monad) -> Action heap key monad
runCont = runM

--------------------------------------------------------------------------------
-- * Primitive Actions

-- | Scheduling is done in terms of a trace of 'Action's. Blocking can
-- only occur as a result of an action, and they cover (most of) the
-- primitives of the concurrency. 'spawn' is absent as it is
-- implemented in terms of 'newEmptyMVar', 'fork', and 'putMVar'.
data Action heap key monad =
    AFork  String ((forall b. M heap key monad b -> M heap key monad b) -> Action heap key monad) (ThreadId -> Action heap key monad)
  | AMyTId (ThreadId -> Action heap key monad)

  | AGetNumCapabilities (Int -> Action heap key monad)
  | ASetNumCapabilities Int (Action heap key monad)

  | forall a. ANewMVar String (MVar key a -> Action heap key monad)
  | forall a. APutMVar     (MVar key a) a (Action heap key monad)
  | forall a. ATryPutMVar  (MVar key a) a (Bool -> Action heap key monad)
  | forall a. AReadMVar    (MVar key a) (a -> Action heap key monad)
  | forall a. ATryReadMVar (MVar key a) (Maybe a -> Action heap key monad)
  | forall a. ATakeMVar    (MVar key a) (a -> Action heap key monad)
  | forall a. ATryTakeMVar (MVar key a) (Maybe a -> Action heap key monad)

  | forall a.   ANewCRef String a (CRef key a -> Action heap key monad)
  | forall a.   AReadCRef    (CRef key a) (a -> Action heap key monad)
  | forall a.   AReadCRefCas (CRef key a) (Ticket a -> Action heap key monad)
  | forall a b. AModCRef     (CRef key a) (a -> (a, b)) (b -> Action heap key monad)
  | forall a b. AModCRefCas  (CRef key a) (a -> (a, b)) (b -> Action heap key monad)
  | forall a.   AWriteCRef   (CRef key a) a (Action heap key monad)
  | forall a.   ACasCRef     (CRef key a) (Ticket a) a ((Bool, Ticket a) -> Action heap key monad)

  | forall e.   Exception e => AThrow e
  | forall e.   Exception e => AThrowTo ThreadId e (Action heap key monad)
  | forall a e. Exception e => ACatching (e -> M heap key monad a) (M heap key monad a) (a -> Action heap key monad)
  | APopCatching (Action heap key monad)
  | forall a. AMasking MaskingState ((forall b. M heap key monad b -> M heap key monad b) -> M heap key monad a) (a -> Action heap key monad)
  | AResetMask Bool Bool MaskingState (Action heap key monad)

  | forall a. AAtom (STMLike heap key monad a) (a -> Action heap key monad)
  | ALift (monad (Action heap key monad))
  | AYield  (Action heap key monad)
  | AReturn (Action heap key monad)
  | ACommit ThreadId CRefId
  | AStop (monad ())

  | forall a. ASub (M heap key monad a) (Either Failure a -> Action heap key monad)
  | AStopSub (Action heap key monad)

--------------------------------------------------------------------------------
-- * Scheduling & Traces

-- | Look as far ahead in the given continuation as possible.
lookahead :: Action heap key monad -> NonEmpty Lookahead
lookahead = fromList . lookahead' where
  lookahead' (AFork _ _ _)           = [WillFork]
  lookahead' (AMyTId _)              = [WillMyThreadId]
  lookahead' (AGetNumCapabilities _) = [WillGetNumCapabilities]
  lookahead' (ASetNumCapabilities i k) = WillSetNumCapabilities i : lookahead' k
  lookahead' (ANewMVar _ _)           = [WillNewMVar]
  lookahead' (APutMVar (MVar c _) _ k)    = WillPutMVar c : lookahead' k
  lookahead' (ATryPutMVar (MVar c _) _ _) = [WillTryPutMVar c]
  lookahead' (AReadMVar (MVar c _) _)     = [WillReadMVar c]
  lookahead' (ATryReadMVar (MVar c _) _)  = [WillTryReadMVar c]
  lookahead' (ATakeMVar (MVar c _) _)     = [WillTakeMVar c]
  lookahead' (ATryTakeMVar (MVar c _) _)  = [WillTryTakeMVar c]
  lookahead' (ANewCRef _ _ _)         = [WillNewCRef]
  lookahead' (AReadCRef (CRef r _) _)     = [WillReadCRef r]
  lookahead' (AReadCRefCas (CRef r _) _)  = [WillReadCRefCas r]
  lookahead' (AModCRef (CRef r _) _ _)    = [WillModCRef r]
  lookahead' (AModCRefCas (CRef r _) _ _) = [WillModCRefCas r]
  lookahead' (AWriteCRef (CRef r _) _ k) = WillWriteCRef r : lookahead' k
  lookahead' (ACasCRef (CRef r _) _ _ _) = [WillCasCRef r]
  lookahead' (ACommit t c)           = [WillCommitCRef t c]
  lookahead' (AAtom _ _)             = [WillSTM]
  lookahead' (AThrow _)              = [WillThrow]
  lookahead' (AThrowTo tid _ k)      = WillThrowTo tid : lookahead' k
  lookahead' (ACatching _ _ _)       = [WillCatching]
  lookahead' (APopCatching k)        = WillPopCatching : lookahead' k
  lookahead' (AMasking ms _ _)       = [WillSetMasking False ms]
  lookahead' (AResetMask b1 b2 ms k) = (if b1 then WillSetMasking else WillResetMasking) b2 ms : lookahead' k
  lookahead' (ALift _)               = [WillLiftIO]
  lookahead' (AYield k)              = WillYield : lookahead' k
  lookahead' (AReturn k)             = WillReturn : lookahead' k
  lookahead' (AStop _)               = [WillStop]
  lookahead' (ASub _ _)              = [WillSubconcurrency]
  lookahead' (AStopSub k)            = WillStopSubconcurrency : lookahead' k
