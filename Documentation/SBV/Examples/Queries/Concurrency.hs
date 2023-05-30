-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.Concurrency
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- When we would like to solve a set of related problems we can use query mode
-- to perform push's and pop's. However performing a push and a pop is still
-- single threaded and so each solution will need to wait for the previous
-- solution to be found. In this example we show a class of functions
-- 'Data.SBV.satConcurrentWithAll' and 'Data.SBV.satConcurrentWithAny' which spin up
-- independent solver instances and runs query computations concurrently. The
-- children query computations are allowed to communicate with one another as
-- demonstrated in the second demo.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.Concurrency where

import Data.SBV
import Data.SBV.Control
import Control.Concurrent
import Control.Monad.IO.Class (liftIO)

-- | Find all solutions to @x + y .== 10@ for positive @x@ and @y@, but at each
-- iteration we would like to ensure that the value of @x@ we get is at least
-- twice as large as the previous one. This is rather silly, but demonstrates
-- how we can dynamically query the result and put in new constraints based on
-- those.
shared :: MVar (SInteger, SInteger) -> Symbolic ()
shared v = do
  x <- sInteger "x"
  y <- sInteger "y"
  constrain $ y .<= 10
  constrain $ x .<= 10
  constrain $ x + y .== 10
  liftIO $ putMVar v (x,y)

-- | In our first query we'll define a constraint that will not be known to the
-- shared or second query and then solve for an answer that will differ from the
-- first query. Note that we need to pass an MVar in so that we can operate on
-- the shared variables. In general, the variables you want to operate on should
-- be defined in the shared part of the query and then passed to the children
-- queries via channels, MVars, or TVars. In this query we constrain x to be
-- less than y and then return the sum of the values. We add a threadDelay just
-- for demonstration purposes
queryOne :: MVar (SInteger, SInteger) -> Query (Maybe Integer)
queryOne v = do
  io $ putStrLn "[One]: Waiting"
  liftIO $ threadDelay 5000000
  io $ putStrLn "[One]: Done"
  (x,y) <- liftIO $ takeMVar v
  constrain $ x .< y

  cs <- checkSat
  case cs of
    Unk    -> error "Too bad, solver said unknown.." -- Won't happen
    DSat{} -> error "Unexpected dsat result.."       -- Won't happen
    Unsat  -> do io $ putStrLn "No other solution!"
                 return Nothing

    Sat    -> do xv <- getValue x
                 yv <- getValue y
                 io $ putStrLn $ "[One]: Current solution is: " ++ show (xv, yv)
                 return $ Just (xv + yv)

-- | In the second query we constrain for an answer where y is smaller than x,
-- and then return the product of the found values.
queryTwo :: MVar (SInteger, SInteger) -> Query (Maybe Integer)
queryTwo v = do
  (x,y) <- liftIO $ takeMVar v
  io $ putStrLn $ "[Two]: got values" ++ show (x,y)
  constrain $ y .< x

  cs <- checkSat
  case cs of
    Unk    -> error "Too bad, solver said unknown.." -- Won't happen
    DSat{} -> error "Unexpected dsat result.."       -- Won't happen
    Unsat  -> do io $ putStrLn "No other solution!"
                 return Nothing

    Sat    -> do yv <- getValue y
                 xv <- getValue x
                 io $ putStrLn $ "[Two]: Current solution is: " ++ show (xv, yv)
                 return $ Just (xv * yv)

-- | Run the demo several times to see that the children threads will change ordering.
demo :: IO ()
demo = do
  v <- newEmptyMVar
  putStrLn "[Main]: Hello from main, kicking off children: "
  results <- satConcurrentWithAll z3 [queryOne v, queryTwo v] (shared v)
  putStrLn "[Main]: Children spawned, waiting for results"
  putStrLn "[Main]: Here they are: "
  print results

-- | Example computation.
sharedDependent :: MVar (SInteger, SInteger) -> Symbolic ()
sharedDependent v = do -- constrain positive and sum:
  x <- sInteger "x"
  y <- sInteger "y"
  constrain $ y .<= 10
  constrain $ x .<= 10
  constrain $ x + y .== 10
  liftIO $ putMVar v (x,y)

-- | In our first query we will make a constrain, solve the constraint and
-- return the values for our variables, then we'll mutate the MVar sending
-- information to the second query. Note that you could use channels, or TVars,
-- or TMVars, whatever you need here, we just use MVars for demonstration
-- purposes. Also note that this effectively creates an ordering between the
-- children queries
firstQuery :: MVar (SInteger, SInteger) -> MVar (SInteger , SInteger) -> Query (Maybe Integer)
firstQuery v1 v2 = do
  (x,y) <- liftIO $ takeMVar v1
  io $ putStrLn "[One]: got vars...working..."
  constrain $ x .< y

  cs <- checkSat
  case cs of
    Unk    -> error "Too bad, solver said unknown.." -- Won't happen
    DSat{} -> error "Unexpected dsat result.."       -- Won't happen
    Unsat  -> do io $ putStrLn "No other solution!"
                 return Nothing

    Sat    -> do xv <- getValue x
                 yv <- getValue y
                 io $ putStrLn $ "[One]: Current solution is: " ++ show (xv, yv)
                 io $ putStrLn   "[One]: Place vars for [Two]"
                 liftIO $ putMVar v2 (literal (xv + yv), literal (xv * yv))
                 return $ Just (xv + yv)

-- | In the second query we create a new variable z, and then a symbolic query
-- using information from the first query and return a solution that uses the
-- new variable and the old variables. Each child query is run in a separate
-- instance of z3 so you can think of this query as driving to a point in the
-- search space, then waiting for more information, once it gets that
-- information it will run a completely separate computation from the first one
-- and return its results.
secondQuery :: MVar (SInteger, SInteger) -> Query (Maybe Integer)
secondQuery v2 = do
  (x,y) <- liftIO $ takeMVar v2
  io $ putStrLn $ "[Two]: got values" ++ show (x,y)
  z <- freshVar "z"
  constrain $ z .> x + y

  cs <- checkSat
  case cs of
    Unk    -> error "Too bad, solver said unknown.." -- Won't happen
    DSat{} -> error "Unexpected dsat result.."       -- Won't happen
    Unsat  -> do io $ putStrLn "No other solution!"
                 return Nothing

    Sat    -> do yv <- getValue y
                 xv <- getValue x
                 zv <- getValue z
                 io $ putStrLn $ "[Two]: My solution is: " ++ show (zv + xv, zv + yv)
                 return $ Just (zv * xv * yv)

-- | In our second demonstration we show how through the use of concurrency
-- constructs the user can have children queries communicate with one another.
-- Note that the children queries are independent and so anything side-effectual
-- like a push or a pop will be isolated to that child thread, unless of course
-- it happens in shared.
demoDependent :: IO ()
demoDependent = do
  v1 <- newEmptyMVar
  v2 <- newEmptyMVar
  results <- satConcurrentWithAll z3 [firstQuery v1 v2, secondQuery v2] (sharedDependent v1)
  print results

{- HLint ignore module "Reduce duplication" -}
