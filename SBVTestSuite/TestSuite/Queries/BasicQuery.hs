-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.BasicQuery
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A hodgepodge of query commands
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.BasicQuery (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Query"
    [ goldenCapturedIO "query1" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} query1
                  appendFile rf ("\n FINAL:" ++ show (SatResult r) ++ "\nDONE!\n")

query1 :: Symbolic SMTResult
query1 = do
       a <- sInteger "a"
       b <- sInteger "b"

       c <- sFloat "c"
       d <- sBool "d"

       e <- sReal "e"

       f :: SInt8 <- free_

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

                  _ <- getOption DiagnosticOutputChannel
                  _ <- getOption ProduceAssertions
                  _ <- getOption ProduceAssignments
                  _ <- getOption ProduceProofs
                  _ <- getOption ProduceUnsatAssumptions
                  _ <- getOption ProduceUnsatCores
                  _ <- getOption RandomSeed
                  _ <- getOption ReproducibleResourceLimit
                  _ <- getOption SMTVerbosity
                  _ <- getOption (OptionKeyword ":smt.mbqi")
                  _ <- getOption (OptionKeyword ":smt.mbqi")

                  _ <- getInfo ReasonUnknown
                  _ <- getInfo (InfoKeyword ":version")
                  _ <- getInfo (InfoKeyword ":status")

                  namedConstraint "later, a > 4" $ a .> 4

                  cs <- checkSat

                  case cs of
                    Sat -> return ()
                    Unk -> getInfo ReasonUnknown >>= error . show
                    r   -> error $ "Something went bad, why not-sat/unk?: " ++ show r

                  setInfo ":status" ["unknown"]

                  _ <- checkSatAssumingWithUnsatisfiableSet [a .> 2]
                  _ <- checkSatAssuming [a .> 2]
                  _ <- getAssignment

                  -- ends up printing different numbers on different machines..
                  -- _ <- getInfo AllStatistics

                  _ <- getInfo AssertionStackLevels
                  _ <- getInfo Authors
                  _ <- getInfo ErrorBehavior
                  _ <- getInfo Name
                  _ <- getInfo ReasonUnknown
                  _ <- getInfo Version
                  _ <- getInfo (InfoKeyword ":memory")
                  _ <- getInfo (InfoKeyword ":time")

                  -- Query a/b
                  av <- getValue a
                  bv <- getValue b

                  _ <- checkSatAssumingWithUnsatisfiableSet [a .> 100,  a .> 9]

                  push 5
                  pop 3
                  _ <- getAssertionStackDepth

                  -- Now assert so that we get even a bigger value..
                  namedConstraint "bey" $ a .> literal (av + bv)
                  namedConstraint "hey" $ a .< literal (av + bv)
                  _ <- checkSat
                  _ <- timeout 80000 getUnsatCore

                  _ <- getProof
                  _ <- timeout 90000 getAssertions

                  echo "there we go"

                  -- fake it!
                  mkSMTResult [ a |-> 332
                              , b |-> 3
                              , c |-> 2.3
                              , d |-> True
                              , e |-> 3.12
                              , f |-> (-12)
                              ]
