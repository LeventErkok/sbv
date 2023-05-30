-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Interpolants
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing a few interpolant computations.
--
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Interpolants (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryInterpolants"
    [ goldenCapturedIO "query_Interpolant1" $ testQuery mathSAT q1
    , goldenCapturedIO "query_Interpolant2" $ testQuery mathSAT q2
    , goldenCapturedIO "query_Interpolant3" $ testQuery z3      q3
    , goldenCapturedIO "query_Interpolant4" $ testQuery z3      q4
    ]

testQuery :: Show a => SMTConfig -> Symbolic a -> FilePath -> IO ()
testQuery s t rf = do r <- runSMTWith s{verbose=True, redirectVerbose=Just rf} t
                      appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

iConstraint :: String -> SBool -> Symbolic ()
iConstraint g = constrainWithAttribute [(":interpolation-group", g)]

q1 :: Symbolic String
q1 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        setOption $ ProduceInterpolants True

        iConstraint "c1" $ a .== b .&& a .== c
        iConstraint "c2" $ b .== d .&& sNot (c .== d)

        query $ do _ <- checkSat
                   getInterpolantMathSAT ["c1"]

q2 :: Symbolic String
q2 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        let f, g :: SInteger -> SInteger
            f = uninterpret "f"
            g = uninterpret "g"

        setOption $ ProduceInterpolants True

        iConstraint "c1" $ f a .== c .&& f b .== d
        iConstraint "c2" $   a .== b .&& g c ./= g d

        query $ do _ <- checkSat
                   getInterpolantMathSAT ["c1"]


q3 :: Symbolic String
q3 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        query $ getInterpolantZ3 [ a .== b .&& a .== c
                                 , b .== d .&& sNot (c .== d)
                                 ]

q4 :: Symbolic String
q4 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        let f, g :: SInteger -> SInteger
            f = uninterpret "f"
            g = uninterpret "g"

        query $ getInterpolantZ3 [ f a .== c .&& f b .== d
                                 ,   a .== b .&& g c ./= g d
                                 ]

{- HLint ignore module "Reduce duplication" -}
