{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : Test.DejaFu.Conc.Internal.Threading
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ExistentialQuantification, RankNTypes
--
-- Operations and types for threads. This module is NOT considered to
-- form part of the public interface of this library.
module Test.DejaFu.Conc.Internal.Threading where

import           Control.Exception                (Exception, MaskingState(..),
                                                   SomeException, fromException)
import           Data.List                        (intersect)
import           Data.Map.Strict                  (Map)
import           Data.Maybe                       (fromMaybe, isJust)

import           Test.DejaFu.Common
import           Test.DejaFu.Conc.Internal.Common

import qualified Data.Map.Strict                  as M

--------------------------------------------------------------------------------
-- * Threads

-- | Threads are stored in a map index by 'ThreadId'.
type Threads heap key monad = Map ThreadId (Thread heap key monad)

-- | All the state of a thread.
data Thread heap key monad = Thread
  { _continuation :: Action heap key monad
  -- ^ The next action to execute.
  , _blocking     :: Maybe BlockedOn
  -- ^ The state of any blocks.
  , _handlers     :: [Handler heap key monad]
  -- ^ Stack of exception handlers
  , _masking      :: MaskingState
  -- ^ The exception masking state.
  }

-- | Construct a thread with just one action
mkthread :: Action heap key monad -> Thread heap key monad
mkthread c = Thread c Nothing [] Unmasked

--------------------------------------------------------------------------------
-- * Blocking

-- | A @BlockedOn@ is used to determine what sort of variable a thread
-- is blocked on.
data BlockedOn = OnMVarFull MVarId | OnMVarEmpty MVarId | OnTVar [TVarId] | OnMask ThreadId deriving Eq

-- | Determine if a thread is blocked in a certain way.
(~=) :: Thread heap key monad -> BlockedOn -> Bool
thread ~= theblock = case (_blocking thread, theblock) of
  (Just (OnMVarFull  _), OnMVarFull  _) -> True
  (Just (OnMVarEmpty _), OnMVarEmpty _) -> True
  (Just (OnTVar      _), OnTVar      _) -> True
  (Just (OnMask      _), OnMask      _) -> True
  _ -> False

--------------------------------------------------------------------------------
-- * Exceptions

-- | An exception handler.
data Handler heap key monad = forall e. Exception e => Handler (e -> Action heap key monad)

-- | Propagate an exception upwards, finding the closest handler
-- which can deal with it.
propagate :: SomeException -> ThreadId -> Threads heap key monad -> Maybe (Threads heap key monad)
propagate e tid threads = case M.lookup tid threads >>= go . _handlers of
  Just (act, hs) -> Just $ except act hs tid threads
  Nothing -> Nothing

  where
    go [] = Nothing
    go (Handler h:hs) = maybe (go hs) (\act -> Just (act, hs)) $ h <$> fromException e

-- | Check if a thread can be interrupted by an exception.
interruptible :: Thread heap key monad -> Bool
interruptible thread = _masking thread == Unmasked || (_masking thread == MaskedInterruptible && isJust (_blocking thread))

-- | Register a new exception handler.
catching :: Exception e => (e -> Action heap key monad) -> ThreadId -> Threads heap key monad -> Threads heap key monad
catching h = M.alter $ \(Just thread) -> Just $ thread { _handlers = Handler h : _handlers thread }

-- | Remove the most recent exception handler.
uncatching :: ThreadId -> Threads heap key monad -> Threads heap key monad
uncatching = M.alter $ \(Just thread) -> Just $ thread { _handlers = tail $ _handlers thread }

-- | Raise an exception in a thread.
except :: Action heap key monad -> [Handler heap key monad] -> ThreadId -> Threads heap key monad -> Threads heap key monad
except act hs = M.alter $ \(Just thread) -> Just $ thread { _continuation = act, _handlers = hs, _blocking = Nothing }

-- | Set the masking state of a thread.
mask :: MaskingState -> ThreadId -> Threads heap key monad -> Threads heap key monad
mask ms = M.alter $ \(Just thread) -> Just $ thread { _masking = ms }

--------------------------------------------------------------------------------
-- * Manipulating threads

-- | Replace the @Action@ of a thread.
goto :: Action heap key monad -> ThreadId -> Threads heap key monad -> Threads heap key monad
goto a = M.alter $ \(Just thread) -> Just (thread { _continuation = a })

-- | Start a thread with the given ID, inheriting the masking state
-- from the parent thread. This ID must not already be in use!
launch :: ThreadId -> ThreadId -> ((forall b. M heap key monad b -> M heap key monad b) -> Action heap key monad) -> Threads heap key monad -> Threads heap key monad
launch parent tid a threads = launch' ms tid a threads where
  ms = fromMaybe Unmasked $ _masking <$> M.lookup parent threads

-- | Start a thread with the given ID and masking state. This must not already be in use!
launch' :: MaskingState -> ThreadId -> ((forall b. M heap key monad b -> M heap key monad b) -> Action heap key monad) -> Threads heap key monad -> Threads heap key monad
launch' ms tid a = M.insert tid thread where
  thread = Thread { _continuation = a umask, _blocking = Nothing, _handlers = [], _masking = ms }

  umask mb = resetMask True Unmasked >> mb >>= \b -> resetMask False ms >> pure b
  resetMask typ m = cont $ \k -> AResetMask typ True m $ k ()

-- | Kill a thread.
kill :: ThreadId -> Threads heap key monad -> Threads heap key monad
kill = M.delete

-- | Block a thread.
block :: BlockedOn -> ThreadId -> Threads heap key monad -> Threads heap key monad
block blockedOn = M.alter doBlock where
  doBlock (Just thread) = Just $ thread { _blocking = Just blockedOn }
  doBlock _ = error "Invariant failure in 'block': thread does NOT exist!"

-- | Unblock all threads waiting on the appropriate block. For 'TVar'
-- blocks, this will wake all threads waiting on at least one of the
-- given 'TVar's.
wake :: BlockedOn -> Threads heap key monad -> (Threads heap key monad, [ThreadId])
wake blockedOn threads = (unblock <$> threads, M.keys $ M.filter isBlocked threads) where
  unblock thread
    | isBlocked thread = thread { _blocking = Nothing }
    | otherwise = thread

  isBlocked thread = case (_blocking thread, blockedOn) of
    (Just (OnTVar tvids), OnTVar blockedOn') -> tvids `intersect` blockedOn' /= []
    (theblock, _) -> theblock == Just blockedOn
