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
    , goldenCapturedIO "query_Interpolant5" $ testQuery z3      q5
    , goldenCapturedIO "query_Interpolant6" $ testQuery z3      q6
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

        setOption $ ProduceInterpolants True

        namedConstraint "c1" $ a .== b .&& a .== c
        namedConstraint "c2" $ b .== d .&& sNot (c .== d)

        query $ do _ <- checkSat
                   getInterpolantZ3 ["c1", "c2"]

q4 :: Symbolic String
q4 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"

        let f, g :: SInteger -> SInteger
            f = uninterpret "f"
            g = uninterpret "g"

        setOption $ ProduceInterpolants True

        namedConstraint "c1" $ f a .== c .&& f b .== d
        namedConstraint "c2" $   a .== b .&& g c ./= g d

        query $ do _ <- checkSat
                   getInterpolantZ3 ["c1", "c2"]

q5 :: Symbolic String
q5 = do x <- sInteger "x"
        y <- sInteger "y"
        z <- sInteger "z"

        a :: SArray Integer Integer <- newArray "a" Nothing
        b :: SArray Integer Integer <- newArray "b" Nothing

        namedConstraint "c1" $ b .== writeArray (writeArray a x 0) y (0::SInteger)
        namedConstraint "c2" $ z .== x .&& readArray b z .== 1

        setOption $ ProduceInterpolants True

        query $ do _ <- checkSat
                   getInterpolantZ3 ["c1", "c2"]

q6 :: Symbolic String
q6 = do a <- sInteger "a"
        b <- sInteger "b"
        c <- sInteger "c"
        d <- sInteger "d"
        e <- sInteger "e"

        namedConstraint "c1" $ a .== b .&& a .== c
        namedConstraint "c2" $ c .== d
        namedConstraint "c3" $ b .== e .&& d ./= e

        setOption $ ProduceInterpolants True

        query $ do _ <- checkSat
                   getInterpolantZ3 ["c1", "c2", "c3"]

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
