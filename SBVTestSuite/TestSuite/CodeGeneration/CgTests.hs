-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.CgTests
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for code-generation features
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.CgTests(tests) where

import Data.SBV.Internals

import Test.Tasty.HUnit (assertEqual)

import Utils.SBVTestFramework

-- | Code-generation tests.
tests :: TestTree
tests = testGroup "CodeGeneration.CgTests"
  [ goldenVsStringShow "selChecked"   $ genSelect True  "selChecked"
  , goldenVsStringShow "selUnchecked" $ genSelect False "selUnChecked"
  , goldenVsStringShow "codeGen1"       foo
  , testCase "collect C runtime requirements" dependencyRequirements
  ]
 where thd (_, _, r) = r

       genSelect b n = thd <$> compileToC' n (do
                         cgSetDriverValues [65]
                         cgPerformRTCs b
                         let sel :: SWord8 -> SWord8
                             sel x = select [1, x+2] 3 x
                         x <- cgInput "x"
                         cgReturn $ sel x)
       foo = thd <$> compileToC' "foo" (do
                        cgSetDriverValues $ repeat 0
                        (x::SInt16)    <- cgInput "x"
                        (ys::[SInt64]) <- cgInputArr 45 "xArr"
                        cgOutput "z" (5 :: SWord16)
                        cgOutputArr "zArr" (replicate 7 (x+1))
                        cgOutputArr "yArr" ys
                        cgReturn (x*2))

-- | Check that ABI kinds and scalar operations contribute the exact external
-- runtime dependencies needed by their generated C bundles.
dependencyRequirements :: Assertion
dependencyRequirements = do
  (_, _, wideBundle) <- compileToC' "requirementsWide" $ do
    value <- cgInput "value" :: SBVCodeGen (SWord 673)
    cgReturn value

  (_, _, fpBundle) <- compileToC' "requirementsFP" $ do
    value <- cgInput "value" :: SBVCodeGen (SFloatingPoint 7 19)
    cgReturn value

  (_, _, integerBundle) <- compileToC' "requirementsInteger" $ do
    value <- cgInput "value" :: SBVCodeGen SInteger
    cgReturn value

  (_, _, nativeFloatBundle) <- compileToC' "requirementsNativeFloat" $ do
    value <- cgInput "value" :: SBVCodeGen SFloat
    cgReturn (fpSqrt sRoundNearestTiesToEven value)

  assertEqual "wide bit-vectors should not add an external library" [[]]              (linkerFlags wideBundle)
  assertEqual "arbitrary floats should request LibBF and libm"       [["-lbf", "-lm"]] (linkerFlags fpBundle)
  assertEqual "exact integers should request GMP"                    [["-lgmp"]]        (linkerFlags integerBundle)
  assertEqual "native floating-point sqrt should request libm"       [["-lm"]]          (linkerFlags nativeFloatBundle)

-- | Extract linker-option lists from the Makefile entries in a generated C
-- bundle.
linkerFlags :: CgPgmBundle -> [[String]]
linkerFlags (CgPgmBundle _ files) = [flags | (_, (CgMakefile flags, _)) <- files]
