-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Interpolants
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing a few interpolant computations.
--
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.Interpolants (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryInterpolants"
    [ goldenCapturedIO "query_Interpolant1" $ testQuery q1
    , goldenCapturedIO "query_Interpolant2" $ testQuery q2
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith mathSAT{verbose=True, redirectVerbose=Just rf} t
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
                   getInterpolant ["c1"]

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
                   getInterpolant ["c1"]

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
