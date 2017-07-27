-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Interpolants
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing a few interpolant computations.
-----------------------------------------------------------------------------
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.Interpolants (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryIndividual"
    [ goldenCapturedIO "query_Interpolant1" $ \rf -> runSMTWith z3{verbose=True, redirectVerbose=Just rf} q1
    ]

q1 :: Symbolic ()
q1 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        setOption $ ProduceInterpolants True

        namedConstraint "c1" $ a .== b &&& a .== c
        namedConstraint "c2" $ b .== d &&& bnot (c .== d)

        query $ do _ <- checkSat
                   _ <- getInterpolant "c1" "c2"
                   return ()
