-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.BasicQuery
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A hodgepodge of query commands
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.BasicQuery (tests)  where

import Data.SBV
import Data.SBV.Control

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Query"
    [ goldenCapturedIO "query1" $ \rf -> print . SatResult =<< runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} query1
    ]

query1 :: Symbolic SMTResult
query1 = do
       a <- sInteger "a"
       b <- sInteger "b"

       c <- sFloat "c"
       d <- sBool "d"

       e <- sReal "e"

       (f :: SWord8) <- free_

       namedConstraint "a > 0" $ a .> 0
       constrain $ b .> 0

       setOption $ ProduceUnsatCores True
       setOption $ ProduceUnsatAssumptions True
       setOption $ ProduceProofs True
       setOption $ RandomSeed 123
       setOption $ ProduceAssertions True
       setOption $ OptionKeyword ":smt.mbqi" ["true"]
       setOption $ ProduceAssignments True

       setInfo ":status" ["sat"]
       setInfo ":bad" ["what"]

       query $ do constrain $ a+2 .>= 5
                  namedConstraint "a+b_<_12" $ a+b .< 12

                  io . print =<< getOption DiagnosticOutputChannel
                  io . print =<< getOption ProduceAssertions
                  io . print =<< getOption ProduceAssignments
                  io . print =<< getOption ProduceProofs
                  io . print =<< getOption ProduceUnsatAssumptions
                  io . print =<< getOption ProduceUnsatCores
                  io . print =<< getOption RandomSeed
                  io . print =<< getOption ReproducibleResourceLimit
                  io . print =<< getOption SMTVerbosity
                  io . print =<< getOption (OptionKeyword ":smt.mbqi")
                  io . print =<< getOption (OptionKeyword ":smt.mbqi")

                  io .print =<< getInfo ReasonUnknown
                  io .print =<< getInfo (InfoKeyword ":version")
                  io .print =<< getInfo (InfoKeyword ":status")

                  namedConstraint "later, a > 4" $ a .> 4

                  cs <- checkSat

                  case cs of
                    Sat -> io $ putStrLn "Everything is OK"
                    Unk -> io .print =<< getInfo ReasonUnknown
                    r   -> error $ "Something went bad, why not-sat/unk?: " ++ show r

                  setInfo ":status" ["unknown"]

                  io . print =<< checkSatAssuming [a .> 2]
                  io . print =<< getAssignment

                  io . print =<< getInfo AllStatistics
                  io . print =<< getInfo AssertionStackLevels
                  io . print =<< getInfo Authors
                  io . print =<< getInfo ErrorBehavior
                  io . print =<< getInfo Name
                  io . print =<< getInfo ReasonUnknown
                  io . print =<< getInfo Version
                  io . print =<< getInfo (InfoKeyword ":memory")
                  io . print =<< getInfo (InfoKeyword ":time")

                  -- Query a/b
                  av <- getValue a
                  bv <- getValue b
                  io $ putStrLn $ "(a,b) = " ++ show (av, bv)

                  io . print =<< checkSatAssuming [a .> 100,  a .> 9]

                  push 5
                  pop 3
                  io . print =<< getAssertionStackDepth

                  -- Now assert so that we get even a bigger value..
                  namedConstraint "bey" $ a .> literal (av + bv)
                  namedConstraint "hey" $ a .< literal (av + bv)
                  _ <- checkSat
                  io . print =<< timeout 4000 getUnsatCore

                  io . putStrLn =<< timeout 7000 getProof
                  io . mapM_ putStrLn =<< timeout 6000 getAssertions

                  echo "there we go"

                  -- fake it!
                  mkSMTResult [ a |-> 332
                              , b |-> 3
                              , c |-> 2.3
                              , d |-> True
                              , e |-> 3.12
                              , f |-> (-12)
                              ]
