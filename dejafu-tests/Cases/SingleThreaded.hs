{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cases.SingleThreaded where

import Control.Exception (ArithException(..), ArrayException(..))
import Data.Maybe (isNothing)
import Test.DejaFu (Failure(..), gives, gives')
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (hUnitTestToTests)
import Test.HUnit (test)
import Test.HUnit.DejaFu (testDejafu)

import Control.Concurrent.Classy
import Test.DejaFu.Conc (Conc, subconcurrency)
import Test.DejaFu.Heap (Heap)

import Utils

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>), (<*>))
#endif

tests :: [Test]
tests =
  [ testGroup "MVar" . hUnitTestToTests $ test
    [ testDejafu emptyMVarTake "empty take" $ gives' [True]
    , testDejafu emptyMVarPut  "empty put"  $ gives' [()]
    , testDejafu emptyMVarRead "empty read" $ gives' [True]
    , testDejafu fullMVarPut   "full put"   $ gives' [True]
    , testDejafu fullMVarTake  "full take"  $ gives' [True]
    , testDejafu fullMVarRead  "full read"  $ gives' [True]
    ]

  , testGroup "CRef" . hUnitTestToTests $ test
    [ testDejafu crefRead       "read"        $ gives' [True]
    , testDejafu crefWrite      "write"       $ gives' [True]
    , testDejafu crefModify     "modify"      $ gives' [True]
    , testDejafu crefTicketPeek "ticket peek" $ gives' [True]
    , testDejafu crefCas1       "cas"         $ gives' [(True, True)]
    , testDejafu crefCas2       "cas (modified)" $ gives' [(False, False)]
    ]

  , testGroup "STM" . hUnitTestToTests $ test
    [ testDejafu stmWrite    "write"   $ gives' [True]
    , testDejafu stmPreserve "write (across transactions)" $ gives' [True]
    , testDejafu stmRetry    "retry"   $ gives  [Left STMDeadlock]
    , testDejafu stmOrElse   "or else" $ gives' [True]
    , testDejafu stmCatch1   "single catch" $ gives' [True]
    , testDejafu stmCatch2   "nested catch" $ gives' [True]
    ]

  , testGroup "Exceptions" . hUnitTestToTests $ test
    [ testDejafu excCatch    "single catch" $ gives' [True]
    , testDejafu excNest     "nested catch" $ gives' [True]
    , testDejafu excEscape   "uncaught"     $ gives  [Left UncaughtException]
    , testDejafu excCatchAll "catch all"    $ gives' [(True, True)]
    , testDejafu excSTM      "from stm"     $ gives' [True]
    , testDejafu excToMain1  "throw to main (uncaught)" $ gives  [Left UncaughtException]
    , testDejafu excToMain2  "throw to main (caught)"   $ gives' [()]
    ]

  , testGroup "Capabilities" . hUnitTestToTests $ test
    [ testDejafu capsGet "get" $ gives' [True]
    , testDejafu capsSet "set" $ gives' [True]
    ]

  , testGroup "Subconcurrency" . hUnitTestToTests $ test
    [ testDejafu scDeadlock1 "deadlock1" $ gives' [Left Deadlock]
    , testDejafu scDeadlock2 "deadlock2" $ gives' [(Left Deadlock, ())]
    , testDejafu scSuccess   "success"   $ gives' [Right ()]
    ]
  ]

--------------------------------------------------------------------------------
-- @MVar@s

-- | An empty @MVar@ cannot be taken from.
emptyMVarTake :: MonadConc m => m Bool
emptyMVarTake = do
  var <- newEmptyMVar
  res <- tryTakeMVar var

  return $ (res :: Maybe ()) == Nothing

-- | An empty @MVar@ can be put into.
emptyMVarPut :: MonadConc m => m ()
emptyMVarPut = do
  var <- newEmptyMVar
  putMVar var ()

-- | An empty @MVar@ cannot be read from.
emptyMVarRead :: MonadConc m => m Bool
emptyMVarRead = do
  var <- newEmptyMVar
  isNothing <$> tryReadMVar var

-- | A full @MVar@ cannot be put into.
fullMVarPut :: MonadConc m => m Bool
fullMVarPut = do
  var <- newMVar ()
  not <$> tryPutMVar var ()

-- | A full @MVar@ can be taken from.
fullMVarTake :: MonadConc m => m Bool
fullMVarTake = do
  var <- newMVar ()
  (() ==) <$> takeMVar var

-- | A full @MVar@ can be read from.
fullMVarRead :: MonadConc m => m Bool
fullMVarRead = do
  var <- newMVar ()
  (() ==) <$> readMVar var

--------------------------------------------------------------------------------
-- @CRef@s

-- | A @CRef@ can be read from.
crefRead :: MonadConc m => m Bool
crefRead = do
  ref <- newCRef (5::Int)
  (5==) <$> readCRef ref

-- | A @CRef@ can be written to.
crefWrite :: MonadConc m => m Bool
crefWrite = do
  ref <- newCRef (5::Int)
  writeCRef ref 6
  (6==) <$> readCRef ref

-- | A @CRef@ can be modified.
crefModify :: MonadConc m => m Bool
crefModify = do
  ref <- newCRef (5::Int)
  atomicModifyCRef ref (\i -> (i+1, ()))
  (6==) <$> readCRef ref

-- | A @Ticket@ contains the value as of when it was created.
crefTicketPeek :: MonadConc m => m Bool
crefTicketPeek = do
  ref  <- newCRef (5::Int)
  tick <- readForCAS ref
  writeCRef ref 6

  (5==) <$> peekTicket tick

-- | A compare-and-swap can be done on a @CRef@ which hasn't been
-- modified.
crefCas1 :: MonadConc m => m (Bool, Bool)
crefCas1 = do
  ref  <- newCRef (5::Int)
  tick <- readForCAS ref

  (suc, _) <- casCRef ref tick 6
  val <- readCRef ref
  return (suc, 6 == val)

-- | A compare-and-swap cannot be done on a @CRef@ which has been
-- modified.
crefCas2 :: MonadConc m => m (Bool, Bool)
crefCas2 = do
  ref  <- newCRef (5::Int)
  tick <- readForCAS ref
  writeCRef ref 6

  (suc, _) <- casCRef ref tick 7
  val <- readCRef ref
  return (suc, 7 == val)

--------------------------------------------------------------------------------
-- STM

-- | A @TVar@ can be written to.
stmWrite :: MonadConc m => m Bool
stmWrite =
  (6==) <$> atomically (do { v <- newTVar (5::Int); writeTVar v 6; readTVar v })

-- | A @TVar@ preserves its value between transactions.
stmPreserve :: MonadConc m => m Bool
stmPreserve = do
  ctv <- atomically $ newTVar (5::Int)
  (5==) <$> atomically (readTVar ctv)

-- | A transaction can be aborted, which blocks the thread.
stmRetry :: MonadConc m => m ()
stmRetry = atomically retry

-- | An abort can be caught by an @orElse@.
stmOrElse :: MonadConc m => m Bool
stmOrElse = do
  ctv <- atomically $ newTVar (5::Int)
  atomically $ orElse retry (writeTVar ctv 6)

  (6==) <$> atomically (readTVar ctv)

-- | An exception can be caught by an appropriate handler.
stmCatch1 :: MonadConc m => m Bool
stmCatch1 = do
  ctv <- atomically $ newTVar (5::Int)
  atomically $ catchArithException
                 (throwSTM Overflow)
                 (\_ -> writeTVar ctv 6)

  (6==) <$> atomically (readTVar ctv)

-- | Nested exception handlers can catch different types of exception.
stmCatch2 :: MonadConc m => m Bool 
stmCatch2 = do
  ctv <- atomically $ newTVar (5::Int)
  atomically $ catchArithException
                 (catchArrayException
                   (throwSTM Overflow)
                   (\_ -> writeTVar ctv 0))
                 (\_ -> writeTVar ctv 6)

  (6==) <$> atomically (readTVar ctv)

--------------------------------------------------------------------------------
-- Exceptions

-- | An exception can be caught by an appropriate handler.
excCatch :: MonadConc m => m Bool
excCatch = catchArithException
  (throw Overflow)
  (\_ -> return True)

-- | Nested exception handlers can catch different types of exception.
excNest :: MonadConc m => m Bool
excNest = catchArithException
  (catchArrayException
    (throw Overflow)
    (\_ -> return False))
  (\_ -> return True)

-- | Exceptions of the wrong type kill the computation
excEscape :: MonadConc m => m ()
excEscape = catchArithException
  (throw $ IndexOutOfBounds "")
  (\_ -> return undefined)

-- | @SomeException@ matches all exception types.
excCatchAll :: MonadConc m => m (Bool, Bool)
excCatchAll = do
  a <- catchSomeException
        (throw Overflow)
        (\_ -> return True)
  b <- catchSomeException
        (throw $ IndexOutOfBounds "")
        (\_ -> return True)

  return (a, b)

-- | Exceptions thrown from STM can be caught.
excSTM :: MonadConc m => m Bool
excSTM = catchArithException
  (atomically $ throwSTM Overflow)
  (\_ -> return True)

-- | Throw an exception to the main thread with 'throwTo', without a
-- handler.
excToMain1 :: MonadConc m => m ()
excToMain1 = do
  tid <- myThreadId
  throwTo tid Overflow

-- | Throw an exception to the main thread with 'throwTo', with a
-- handler.
excToMain2 :: MonadConc m => m ()
excToMain2 = do
  tid <- myThreadId
  catchArithException (throwTo tid Overflow) (\_ -> pure ())

--------------------------------------------------------------------------------
-- Capabilities

-- | Check that the capabilities are consistent when retrieved.
capsGet :: MonadConc m => m Bool
capsGet = (==) <$> getNumCapabilities <*> getNumCapabilities

-- | Check that the capabilities can be set.
capsSet :: MonadConc m => m Bool
capsSet = do
  caps <- getNumCapabilities
  setNumCapabilities $ caps + 1
  (== caps + 1) <$> getNumCapabilities

--------------------------------------------------------------------------------
-- Subconcurrency

-- | Subcomputation deadlocks.
scDeadlock1 :: Heap heap key monad => Conc heap key monad (Either Failure ())
scDeadlock1 = subconcurrency (newEmptyMVar >>= readMVar)

-- | Subcomputation deadlocks, and action after it still happens.
scDeadlock2 :: Heap heap key monad => Conc heap key monad (Either Failure (), ())
scDeadlock2 = do
  var <- newMVar ()
  (,) <$> subconcurrency (putMVar var ()) <*> readMVar var

-- | Subcomputation successfully completes.
scSuccess :: Heap heap key monad => Conc heap key monad (Either Failure ())
scSuccess = do
  var <- newMVar ()
  subconcurrency (takeMVar var)
