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
    , goldenCapturedIO "query_Interpolant2" $ \rf -> runSMTWith z3{verbose=True, redirectVerbose=Just rf} q2
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

q2 :: Symbolic ()
q2 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        let f, g :: SInteger -> SInteger
            f = uninterpret "f"
            g = uninterpret "g"

        setOption $ ProduceInterpolants True

        namedConstraint "c1" $ f a .== c &&& f b .== d
        namedConstraint "c2" $   a .== b &&& g c ./= g d

        query $ do _ <- checkSat
                   _ <- getInterpolant "c1" "c2"
                   return ()
