{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : Test.DejaFu.Conc.Internal.Memory
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : BangPatterns, FlexibleContexts, GADTs MultiParamTypeClasses
--
-- Operations over @CRef@s and @MVar@s. This module is NOT considered
-- to form part of the public interface of this library.
--
-- Relaxed memory operations over @CRef@s are implemented with an
-- explicit write buffer: one per thread for TSO, and one per
-- thread/variable combination for PSO. Unsynchronised writes append
-- to this buffer, and periodically separate threads commit from these
-- buffers to the \"actual\" @CRef@.
--
-- This model comes from /Dynamic Partial Order Reduction for Relaxed
-- Memory Models/, N. Zhang, M. Kusano, and C. Wang (2015).
module Test.DejaFu.Conc.Internal.Memory where

import           Data.Map.Strict                     (Map)
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (fromJust, isJust)
import           Data.Monoid                         ((<>))
import           Data.Sequence                       (Seq, ViewL(..), singleton,
                                                      viewl, (><))

import           Test.DejaFu.Common
import           Test.DejaFu.Conc.Internal.Common
import           Test.DejaFu.Conc.Internal.Threading
import qualified Test.DejaFu.Heap                    as H


--------------------------------------------------------------------------------
-- * Manipulating @CRef@s

-- | In non-sequentially-consistent memory models, non-synchronised
-- writes get buffered.
--
-- The @CRefId@ parameter is only used under PSO. Under TSO each
-- thread has a single buffer.
newtype WriteBuffer key = WriteBuffer
  { buffer :: Map (ThreadId, Maybe CRefId) (Seq (BufferedWrite key)) }

-- | A buffered write is a reference to the variable, and the value to
-- write. Universally quantified over the value type so that the only
-- thing which can be done with it is to write it to the reference.
data BufferedWrite key where
  BufferedWrite :: ThreadId -> CRef key a -> a -> BufferedWrite key

-- | An empty write buffer.
emptyBuffer :: WriteBuffer key
emptyBuffer = WriteBuffer M.empty

-- | Add a new write to the end of a buffer.
bufferWrite :: H.Heap heap key monad
  => WriteBuffer key -> (ThreadId, Maybe CRefId) -> CRef key a -> a
  -> heap -> (heap, WriteBuffer key)
bufferWrite (WriteBuffer wb) k@(tid, _) cref@(CRef _ key) new heap =
  let
    -- construct the new write buffer
    write   = singleton $ BufferedWrite tid cref new
    buffer' = WriteBuffer $ M.insertWith (flip (><)) k write wb

    -- write the thread-local value to the @CRef@'s update map.
    (locals, count, def) = H.lookup key heap
    update (Just (_, n)) = (new, n + 1)
    update Nothing       = (new, 1)
    heap' = H.set key (M.alter (Just . update) tid locals, count, def) heap
  in (heap', buffer')

-- | Commit the write at the head of a buffer.
commitWrite :: H.Heap heap key monad
  => WriteBuffer key -> (ThreadId, Maybe CRefId)
  -> heap -> (heap, WriteBuffer key)
commitWrite w@(WriteBuffer wb) k heap = case maybe EmptyL viewl $ M.lookup k wb of
  BufferedWrite _ cref a :< rest -> (writeImmediate cref a heap, WriteBuffer $ M.insert k rest wb)
  EmptyL -> (heap, w)

-- | Read from a @CRef@, returning a newer thread-local non-committed
-- write if there is one.
readCRef :: H.Heap heap key monad => CRef key a -> ThreadId -> heap -> a
readCRef cref tid heap =
  let (val, _, _) = readCRefPrim cref tid heap
  in val

-- | Read from a @CRef@, returning a @Ticket@ representing the current
-- view of the thread.
readForTicket :: H.Heap heap key monad => CRef key a -> ThreadId -> heap -> Ticket a
readForTicket cref@(CRef crid _) tid heap =
  let (val, gcount, mcount) = readCRefPrim cref tid heap
  in Ticket crid gcount mcount val

-- | Perform a compare-and-swap on a @CRef@ if the ticket is still
-- valid. This is strict in the \"new\" value argument.
casCRef :: H.Heap heap key monad => CRef key a -> ThreadId -> Ticket a -> a -> heap -> (heap, Bool, Ticket a)
casCRef cref tid (Ticket _ gw mw _) !new heap =
  let tick'@(Ticket _ gw' mw' _) = readForTicket cref tid heap
  in if (gw, mw) == (gw', mw')
     then
       let heap'  = writeImmediate cref new heap
           tick'' = readForTicket cref tid heap'
       in (heap', True, tick'')
     else (heap, False, tick')

-- | Read the local state of a @CRef@.
readCRefPrim :: H.Heap heap key monad => CRef key a -> ThreadId -> heap -> (a, Integer, Integer)
readCRefPrim (CRef _ key) tid heap =
  let (vals, gcount, def) = H.lookup key heap
      (val, mcount) = M.findWithDefault (def, 0) tid vals
  in (val, gcount, mcount)

-- | Write and commit to a @CRef@ immediately, clearing the update map
-- and incrementing the write count.
writeImmediate :: H.Heap heap key monad => CRef key a -> a -> heap -> heap
writeImmediate (CRef _ key) a heap =
  let (_, count, _) = H.lookup key heap
  in H.set key (M.empty, count + 1, a) heap

-- | Flush all writes in the buffer.
writeBarrier :: H.Heap heap key monad => WriteBuffer key -> heap -> heap
writeBarrier (WriteBuffer wb) heap = foldr flush heap wb where
  flush bws h0 = foldr (\(BufferedWrite _ cref a) -> writeImmediate cref a) h0 bws

-- | Add phantom threads to the thread list to commit pending writes.
addCommitThreads :: WriteBuffer r -> Threads heap key monad -> Threads heap key monad
addCommitThreads (WriteBuffer wb) ts = ts <> M.fromList phantoms where
  phantoms = [ (ThreadId Nothing $ negate tid, mkthread $ fromJust c)
             | ((_, b), tid) <- zip (M.toList wb) [1..]
             , let c = go $ viewl b
             , isJust c]
  go (BufferedWrite tid (CRef crid _) _ :< _) = Just $ ACommit tid crid
  go EmptyL = Nothing

-- | Remove phantom threads.
delCommitThreads :: Threads heap key monad -> Threads heap key monad
delCommitThreads = M.filterWithKey $ \k _ -> k >= initialThread

--------------------------------------------------------------------------------
-- * Manipulating @MVar@s

-- | Put into a @MVar@, blocking if full.
putIntoMVar :: H.Heap heap key monad
  => MVar key a -> a -> Action heap key monad -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
putIntoMVar cvar a c = mutMVar True cvar a (const c)

-- | Try to put into a @MVar@, not blocking if full.
tryPutIntoMVar :: H.Heap heap key monad
  => MVar key a -> a -> (Bool -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
tryPutIntoMVar = mutMVar False

-- | Read from a @MVar@, blocking if empty.
readFromMVar :: H.Heap heap key monad
  => MVar key a -> (a -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
readFromMVar cvar c = seeMVar False True cvar (c . fromJust)

-- | Try to read from a @MVar@, not blocking if empty.
tryReadFromMVar :: H.Heap heap key monad
  => MVar key a -> (Maybe a -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
tryReadFromMVar = seeMVar False False

-- | Take from a @MVar@, blocking if empty.
takeFromMVar :: H.Heap heap key monad
  => MVar key a -> (a -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
takeFromMVar cvar c = seeMVar True True cvar (c . fromJust)

-- | Try to take from a @MVar@, not blocking if empty.
tryTakeFromMVar :: H.Heap heap key monad
  => MVar key a -> (Maybe a -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
tryTakeFromMVar = seeMVar True False

-- | Mutate a @MVar@, in either a blocking or nonblocking way.
mutMVar :: H.Heap heap key monad
  => Bool -> MVar key a -> a -> (Bool -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
mutMVar blocking (MVar cvid key) a c threadid threads heap =
  let val = H.lookup key heap
  in case val of
       Just _
         | blocking ->
           let threads' = block (OnMVarEmpty cvid) threadid threads
           in (heap, False, threads', [])
         | otherwise ->
           (heap, False, goto (c False) threadid threads, [])
       Nothing ->
         let (threads', woken) = wake (OnMVarFull cvid) threads
             heap' = H.set key (Just a) heap
         in (heap', True, goto (c True) threadid threads', woken)

-- | Read a @MVar@, in either a blocking or nonblocking
-- way.
seeMVar :: H.Heap heap key monad
  => Bool -> Bool -> MVar key a -> (Maybe a -> Action heap key monad) -> ThreadId -> Threads heap key monad
  -> heap -> (heap, Bool, Threads heap key monad, [ThreadId])
seeMVar emptying blocking (MVar cvid key) c threadid threads heap =
  let val = H.lookup key heap
  in case val of
    Just _ ->
      let heap' = if emptying then H.set key Nothing heap else heap
          (threads', woken) = wake (OnMVarEmpty cvid) threads
      in (heap', True, goto (c val) threadid threads', woken)
    Nothing
      | blocking ->
        let threads' = block (OnMVarFull cvid) threadid threads
        in (heap, False, threads', [])
      | otherwise ->
        (heap, False, goto (c Nothing) threadid threads, [])
