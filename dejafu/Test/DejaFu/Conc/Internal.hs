{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Test.DejaFu.Conc.Internal
-- Copyright   : (c) 2016 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : FlexibleContexts, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables
--
-- Concurrent monads with a fixed scheduler: internal types and
-- functions. This module is NOT considered to form part of the public
-- interface of this library.
module Test.DejaFu.Conc.Internal where

import           Control.Exception                   (MaskingState(..),
                                                      toException)
import           Control.Monad.Ref                   (MonadRef, readRef,
                                                      writeRef)
import qualified Data.Foldable                       as F
import           Data.List                           (sort)
import           Data.List.NonEmpty                  (NonEmpty(..), fromList)
import qualified Data.Map.Strict                     as M
import           Data.Maybe                          (fromJust, isJust,
                                                      isNothing)
import           Data.Monoid                         ((<>))
import           Data.Sequence                       (Seq, (<|))
import qualified Data.Sequence                       as Seq

import           Test.DejaFu.Common
import           Test.DejaFu.Conc.Internal.Common
import           Test.DejaFu.Conc.Internal.Memory
import           Test.DejaFu.Conc.Internal.Threading
import qualified Test.DejaFu.Heap                    as H
import           Test.DejaFu.Schedule
import           Test.DejaFu.STM                     (Result(..),
                                                      runTransaction)

--------------------------------------------------------------------------------
-- * Execution

-- | 'Trace' but as a sequence.
type SeqTrace
  = Seq (Decision, [(ThreadId, NonEmpty Lookahead)], ThreadAction)

-- | Run a concurrent computation with a given 'Scheduler' and initial
-- state, returning a failure reason on error. Also returned is the
-- final state of the scheduler, and an execution trace.
runConcurrency :: (H.Heap heap key monad, MonadRef r monad)
  => Scheduler g
  -> MemType
  -> g
  -> IdSource
  -> Int
  -> heap
  -> M heap key monad a
  -> monad (Either Failure a, Context heap key monad g, SeqTrace, Maybe (ThreadId, ThreadAction))
runConcurrency sched memtype g idsrc caps heap ma = do
  (c, ref) <- runRefCont AStop (Just . Right) (runM ma)
  let ctx = Context { cHeap       = heap
                    , cSchedState = g
                    , cIdSource   = idsrc
                    , cThreads    = launch' Unmasked initialThread (const c) M.empty
                    , cWriteBuf   = emptyBuffer
                    , cCaps       = caps
                    }
  (finalCtx, trace, finalAction) <- runThreads sched memtype ref ctx
  out <- readRef ref
  pure (fromJust out, finalCtx, trace, finalAction)

-- | The context a collection of threads are running in.
data Context heap key monad g = Context
  { cHeap       :: heap
  , cSchedState :: g
  , cIdSource   :: IdSource
  , cThreads    :: Threads heap key monad
  , cWriteBuf   :: WriteBuffer key
  , cCaps       :: Int
  }

-- | Run a collection of threads, until there are no threads left.
runThreads :: (H.Heap heap key monad, MonadRef r monad)
  => Scheduler g
  -> MemType
  -> r (Maybe (Either Failure a))
  -> Context heap key monad g
  -> monad (Context heap key monad g, SeqTrace, Maybe (ThreadId, ThreadAction))
runThreads sched memtype ref = go Seq.empty [] Nothing where
  -- sofar is the 'SeqTrace', sofarSched is the @[(Decision,
  -- ThreadAction)]@ trace the scheduler needs.
  go sofar sofarSched prior ctx
    | isTerminated  = pure (ctx, sofar, prior)
    | isDeadlocked  = die sofar prior Deadlock ctx
    | isSTMLocked   = die sofar prior STMDeadlock ctx
    | isAborted     = die sofar prior Abort $ ctx { cSchedState = g' }
    | isNonexistant = die sofar prior InternalError $ ctx { cSchedState = g' }
    | isBlocked     = die sofar prior InternalError $ ctx { cSchedState = g' }
    | otherwise = do
      stepped <- stepThread sched memtype chosen (_continuation $ fromJust thread) $ ctx { cSchedState = g' }
      case stepped of
        (Right ctx', actOrTrc) ->
          let (_, trc) = getActAndTrc actOrTrc
              threads' = if (interruptible <$> M.lookup chosen (cThreads ctx')) /= Just False
                         then unblockWaitingOn chosen (cThreads ctx')
                         else cThreads ctx'
              sofarSched' = sofarSched <> map (\(d,_,a) -> (d,a)) (F.toList trc)
              ctx'' = ctx' { cThreads = delCommitThreads threads' }
          in go (sofar <> trc) sofarSched' (getPrior actOrTrc) ctx''
        (Left failure, actOrTrc) ->
          let (_, trc) = getActAndTrc actOrTrc
              ctx'     = ctx { cSchedState = g', cThreads = delCommitThreads threads }
          in die (sofar <> trc) (getPrior actOrTrc) failure ctx'

    where
      (choice, g')  = sched sofarSched prior (fromList $ map (\(t,l:|_) -> (t,l)) runnable') (cSchedState ctx)
      chosen        = fromJust choice
      runnable'     = [(t, nextActions t) | t <- sort $ M.keys runnable]
      runnable      = M.filter (isNothing . _blocking) threadsc
      thread        = M.lookup chosen threadsc
      threadsc      = addCommitThreads (cWriteBuf ctx) threads
      threads       = cThreads ctx
      isAborted     = isNothing choice
      isBlocked     = isJust . _blocking $ fromJust thread
      isNonexistant = isNothing thread
      isTerminated  = initialThread `notElem` M.keys threads
      isDeadlocked  = M.null (M.filter (isNothing . _blocking) threads) &&
        (((~=  OnMVarFull  undefined) <$> M.lookup initialThread threads) == Just True ||
         ((~=  OnMVarEmpty undefined) <$> M.lookup initialThread threads) == Just True ||
         ((~=  OnMask      undefined) <$> M.lookup initialThread threads) == Just True)
      isSTMLocked = M.null (M.filter (isNothing . _blocking) threads) &&
        ((~=  OnTVar []) <$> M.lookup initialThread threads) == Just True

      unblockWaitingOn tid = fmap unblock where
        unblock thrd = case _blocking thrd of
          Just (OnMask t) | t == tid -> thrd { _blocking = Nothing }
          _ -> thrd

      decision
        | Just chosen == (fst <$> prior) = Continue
        | (fst <$> prior) `notElem` map (Just . fst) runnable' = Start chosen
        | otherwise = SwitchTo chosen

      nextActions t = lookahead . _continuation . fromJust $ M.lookup t threadsc

      die sofar' finalDecision reason finalCtx = do
        writeRef ref (Just $ Left reason)
        pure (finalCtx, sofar', finalDecision)

      getActAndTrc (Single a)    = (a, Seq.singleton (decision, runnable', a))
      getActAndTrc (SubC   as _) = (Subconcurrency, (decision, runnable', Subconcurrency) <| as)

      getPrior (Single a)      = Just (chosen, a)
      getPrior (SubC _ finalD) = finalD

--------------------------------------------------------------------------------
-- * Single-step execution

-- | What a thread did.
data Act
  = Single ThreadAction
  -- ^ Just one action.
  | SubC SeqTrace (Maybe (ThreadId, ThreadAction))
  -- ^ Subconcurrency, with the given trace and final action.
  deriving (Eq, Show)

-- | Run a single thread one step, by dispatching on the type of
-- 'Action'.
stepThread :: forall heap key monad r g. (H.Heap heap key monad, MonadRef r monad)
  => Scheduler g
  -- ^ The scheduler.
  -> MemType
  -- ^ The memory model to use.
  -> ThreadId
  -- ^ ID of the current thread
  -> Action heap key monad
  -- ^ Action to step
  -> Context heap key monad g
  -- ^ The execution context.
  -> monad (Either Failure (Context heap key monad g), Act)
stepThread sched memtype tid action ctx = case action of
    -- start a new thread, assigning it the next 'ThreadId'
    AFork n a b -> pure $
        let threads' = launch tid newtid a (cThreads ctx)
            (idSource', newtid) = nextTId n (cIdSource ctx)
        in (Right ctx { cThreads = goto (b newtid) tid threads', cIdSource = idSource' }, Single (Fork newtid))

    -- get the 'ThreadId' of the current thread
    AMyTId c -> simple (cHeap ctx) (goto (c tid) tid (cThreads ctx)) MyThreadId

    -- get the number of capabilities
    AGetNumCapabilities c -> simple (cHeap ctx) (goto (c (cCaps ctx)) tid (cThreads ctx)) $ GetNumCapabilities (cCaps ctx)

    -- set the number of capabilities
    ASetNumCapabilities i c -> pure
      (Right ctx { cThreads = goto c tid (cThreads ctx), cCaps = i }, Single (SetNumCapabilities i))

    -- yield the current thread
    AYield c -> simple (cHeap ctx) (goto c tid (cThreads ctx)) Yield

    -- create a new @MVar@, using the next 'MVarId'.
    ANewMVar n c -> do
      let (idSource', newmvid) = nextMVId n (cIdSource ctx)
      (key, heap') <- H.insert Nothing (cHeap ctx)
      let mvar = MVar newmvid key
      pure (Right ctx { cHeap = heap', cThreads = goto (c mvar) tid (cThreads ctx), cIdSource = idSource' }, Single (NewMVar newmvid))

    -- put a value into a @MVar@, blocking the thread until it's empty.
    APutMVar cvar@(MVar cvid _) a c -> synchronised $
      let (heap', success, threads', woken) = putIntoMVar cvar a c tid (cThreads ctx) (cHeap ctx)
      in simple heap' threads' $ if success then PutMVar cvid woken else BlockedPutMVar cvid

    -- try to put a value into a @MVar@, without blocking.
    ATryPutMVar cvar@(MVar cvid _) a c -> synchronised $
      let (heap', success, threads', woken) = tryPutIntoMVar cvar a c tid (cThreads ctx) (cHeap ctx)
      in simple heap' threads' $ TryPutMVar cvid success woken

    -- get the value from a @MVar@, without emptying, blocking the
    -- thread until it's full.
    AReadMVar cvar@(MVar cvid _) c -> synchronised $
      let (heap', success, threads', _) = readFromMVar cvar c tid (cThreads ctx) (cHeap ctx)
      in simple heap' threads' $ if success then ReadMVar cvid else BlockedReadMVar cvid

    -- try to get the value from a @MVar@, without emptying, without
    -- blocking.
    ATryReadMVar cvar@(MVar cvid _) c -> synchronised $
      let (heap', success, threads', _) = tryReadFromMVar cvar c tid (cThreads ctx) (cHeap ctx)
      in simple heap' threads' $ TryReadMVar cvid success

    -- take the value from a @MVar@, blocking the thread until it's
    -- full.
    ATakeMVar cvar@(MVar cvid _) c -> synchronised $
      let (heap', success, threads', woken) = takeFromMVar cvar c tid (cThreads ctx) (cHeap ctx)
      in simple heap' threads' $ if success then TakeMVar cvid woken else BlockedTakeMVar cvid

    -- try to take the value from a @MVar@, without blocking.
    ATryTakeMVar cvar@(MVar cvid _) c -> synchronised $
      let (heap', success, threads', woken) = tryTakeFromMVar cvar c tid (cThreads ctx) (cHeap ctx)
      in simple heap' threads' $ TryTakeMVar cvid success woken

    -- create a new @CRef@, using the next 'CRefId'.
    ANewCRef n a c -> do
      let (idSource', newcrid) = nextCRId n (cIdSource ctx)
      (key, heap') <- H.insert (M.empty, 0, a) (cHeap ctx)
      let cref = CRef newcrid key
      pure (Right ctx { cHeap = heap', cThreads = goto (c cref) tid (cThreads ctx), cIdSource = idSource' }, Single (NewCRef newcrid))

    -- read from a @CRef@.
    AReadCRef cref@(CRef crid _) c ->
      let val = readCRef cref tid (cHeap ctx)
      in simple (cHeap ctx) (goto (c val) tid (cThreads ctx)) $ ReadCRef crid

    -- read from a @CRef@ for future compare-and-swap operations.
    AReadCRefCas cref@(CRef crid _) c ->
      let tick = readForTicket cref tid (cHeap ctx)
      in simple (cHeap ctx) (goto (c tick) tid (cThreads ctx)) $ ReadCRefCas crid

    -- modify a @CRef@.
    AModCRef cref@(CRef crid _) f c -> synchronised $
      let (new, val) = f (readCRef cref tid (cHeap ctx))
          heap' = writeImmediate cref new (cHeap ctx)
      in simple heap' (goto (c val) tid (cThreads ctx)) $ ModCRef crid

    -- modify a @CRef@ using a compare-and-swap.
    AModCRefCas cref@(CRef crid _) f c -> synchronised $
      let tick@(Ticket _ _ _ old) = readForTicket cref tid (cHeap ctx)
          (new, val) = f old
          (heap', _, _) = casCRef cref tid tick new (cHeap ctx)
      in simple heap' (goto (c val) tid (cThreads ctx)) $ ModCRefCas crid

    -- write to a @CRef@ without synchronising.
    AWriteCRef cref@(CRef crid _) a c -> case memtype of
      -- write immediately.
      SequentialConsistency ->
        let heap' = writeImmediate cref a (cHeap ctx)
        in simple heap' (goto c tid (cThreads ctx)) $ WriteCRef crid
      -- add to buffer using thread id.
      TotalStoreOrder ->
        let (heap', wb') = bufferWrite (cWriteBuf ctx) (tid, Nothing) cref a (cHeap ctx)
        in pure (Right ctx { cHeap = heap', cThreads = goto c tid (cThreads ctx), cWriteBuf = wb' }, Single (WriteCRef crid))
      -- add to buffer using both thread id and cref id
      PartialStoreOrder ->
        let (heap', wb') = bufferWrite (cWriteBuf ctx) (tid, Just crid) cref a (cHeap ctx)
        in pure (Right ctx { cHeap = heap', cThreads = goto c tid (cThreads ctx), cWriteBuf = wb' }, Single (WriteCRef crid))

    -- perform a compare-and-swap on a @CRef@.
    ACasCRef cref@(CRef crid _) tick a c -> synchronised $
      let (heap', suc, tick') = casCRef cref tid tick a (cHeap ctx)
      in simple heap' (goto (c (suc, tick')) tid (cThreads ctx)) $ CasCRef crid suc

    -- commit a @CRef@ write
    ACommit t c ->
      let (heap', wb') = case memtype of
            -- shouldn't ever get here
            SequentialConsistency ->
              error "Attempting to commit under SequentialConsistency"
            -- commit using the thread id.
            TotalStoreOrder ->
              commitWrite (cWriteBuf ctx) (t, Nothing) (cHeap ctx)
            -- commit using the cref id.
            PartialStoreOrder ->
              commitWrite (cWriteBuf ctx) (t, Just c) (cHeap ctx)
      in pure (Right ctx { cHeap = heap', cWriteBuf = wb' }, Single (CommitCRef t c))

    -- run a STM transaction atomically.
    AAtom stm c -> synchronised $ do
      (heap', res, idSource', trace) <- runTransaction stm (cIdSource ctx) (cHeap ctx)
      case res of
        Success _ written val ->
          let (threads', woken) = wake (OnTVar written) (cThreads ctx)
          in pure (Right ctx { cHeap = heap', cThreads = goto (c val) tid threads', cIdSource = idSource' }, Single (STM trace woken))
        Retry touched ->
          let threads' = block (OnTVar touched) tid (cThreads ctx)
          in pure (Right ctx { cHeap = heap', cThreads = threads', cIdSource = idSource'}, Single (BlockedSTM trace))
        Exception e -> do
          let act = STM trace []
          res' <- stepThrow heap' tid (cThreads ctx) act e
          pure $ case res' of
            (Right ctx', _) -> (Right ctx', Single act)
            (Left err, _) -> (Left err, Single act)

    -- lift an action from the underlying monad into the @Conc@
    -- computation.
    ALift na -> do
      a <- na
      simple (cHeap ctx) (goto a tid (cThreads ctx)) LiftIO

    -- throw an exception, and propagate it to the appropriate
    -- handler.
    AThrow e -> stepThrow (cHeap ctx) tid (cThreads ctx) Throw e

    -- throw an exception to the target thread, and propagate it to
    -- the appropriate handler.
    AThrowTo t e c -> synchronised $
      let threads' = goto c tid (cThreads ctx)
          blocked  = block (OnMask t) tid (cThreads ctx)
      in case M.lookup t (cThreads ctx) of
           Just thread
             | interruptible thread -> stepThrow (cHeap ctx) t threads' (ThrowTo t) e
             | otherwise -> simple (cHeap ctx) blocked $ BlockedThrowTo t
           Nothing -> simple (cHeap ctx) threads' $ ThrowTo t

    -- run a subcomputation in an exception-catching context.
    ACatching h ma c ->
      let a        = runCont ma      (APopCatching . c)
          e exc    = runCont (h exc) (APopCatching . c)
          threads' = goto a tid (catching e tid (cThreads ctx))
      in simple (cHeap ctx) threads' Catching

    -- pop the top exception handler from the thread's stack.
    APopCatching a ->
      let threads' = goto a tid (uncatching tid (cThreads ctx))
      in simple (cHeap ctx) threads' PopCatching

    -- execute a subcomputation with a new masking state, and give it
    -- a function to run a computation with the current masking state.
    AMasking m ma c ->
      let a = runCont (ma umask) (AResetMask False False m' . c)
          m' = _masking . fromJust $ M.lookup tid (cThreads ctx)
          umask mb = resetMask True m' >> mb >>= \b -> resetMask False m >> pure b
          resetMask typ ms = cont $ \k -> AResetMask typ True ms $ k ()
          threads' = goto a tid (mask m tid (cThreads ctx))
      in simple (cHeap ctx) threads' $ SetMasking False m


    -- reset the masking thread of the state.
    AResetMask b1 b2 m c ->
      let act      = (if b1 then SetMasking else ResetMasking) b2 m
          threads' = goto c tid (mask m tid (cThreads ctx))
      in simple (cHeap ctx) threads' act

    -- execute a 'return' or 'pure'.
    AReturn c -> simple (cHeap ctx) (goto c tid (cThreads ctx)) Return

    -- kill the current thread.
    AStop na -> na >> simple (cHeap ctx) (kill tid (cThreads ctx)) Stop

    -- run a subconcurrent computation.
    ASub ma c
      | M.size (cThreads ctx) > 1 -> pure (Left IllegalSubconcurrency, Single Subconcurrency)
      | otherwise -> do
          (res, ctx', trace, finalDecision) <-
            runConcurrency sched memtype (cSchedState ctx) (cIdSource ctx) (cCaps ctx) (cHeap ctx) ma
          pure (Right ctx { cHeap       = cHeap ctx'
                          , cThreads    = goto (AStopSub (c res)) tid (cThreads ctx)
                          , cIdSource   = cIdSource ctx'
                          , cSchedState = cSchedState ctx' }, SubC trace finalDecision)

    -- after the end of a subconcurrent computation. does nothing,
    -- only exists so that: there is an entry in the trace for
    -- returning to normal computation; and every item in the trace
    -- corresponds to a scheduling point.
    AStopSub c -> simple (cHeap ctx) (goto c tid (cThreads ctx)) StopSubconcurrency
  where

    -- this is not inline in the long @case@ above as it's needed by
    -- @AAtom@, @AThrow@, and @AThrowTo@.
    stepThrow heap t ts act e =
      case propagate (toException e) t ts of
        Just ts' -> simple heap ts' act
        Nothing
          | t == initialThread -> pure (Left UncaughtException, Single act)
          | otherwise -> simple heap (kill t ts) act

    -- helper for actions which only change the threads.
    simple heap' threads' act = pure (Right ctx { cHeap = heap', cThreads = threads' }, Single act)

    -- helper for actions impose a write barrier.
    synchronised ma = do
      res <- ma
      pure $ case res of
        (Right ctx', act) -> (Right ctx' { cHeap = writeBarrier (cWriteBuf ctx) (cHeap ctx'), cWriteBuf = emptyBuffer }, act)
        _ -> res
