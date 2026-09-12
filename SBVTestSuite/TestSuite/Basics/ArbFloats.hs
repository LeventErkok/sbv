-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ArbFloats
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Basic arbitrary float checks
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.ArbFloats(tests) where

import Utils.SBVTestFramework
import Test.Tasty.HUnit (assertEqual)

-- | Number of inhabitants: @2^sb(2^eb - 1) + 3@.
count :: Integer -> Integer -> Integer
count eb sb = 2^sb * (2^eb - 1) + 3

-- | Concrete and symbolic arbitrary-format floating-point checks.
tests :: TestTree
tests = testGroup "Basics.ArbFloats"
  [ testCase "integral conversion rounding" integralConversionRounding
  , testCase "integral conversion format widths" integralConversionWidths
  , testCase "symbolic integral conversion rounding" symbolicIntegralConversionRounding
  , testCase "FP_2_2" (assert $ (== fromIntegral (count 2 2)) <$> numberOfModels (const sTrue :: SFloatingPoint 2 2 -> SBool))
  , testCase "FP_2_3" (assert $ (== fromIntegral (count 2 3)) <$> numberOfModels (const sTrue :: SFloatingPoint 2 3 -> SBool))
  , testCase "FP_2_4" (assert $ (== fromIntegral (count 2 4)) <$> numberOfModels (const sTrue :: SFloatingPoint 2 4 -> SBool))

  , testCase "FP_3_2" (assert $ (== fromIntegral (count 3 2)) <$> numberOfModels (const sTrue :: SFloatingPoint 3 2 -> SBool))
  , testCase "FP_3_3" (assert $ (== fromIntegral (count 3 3)) <$> numberOfModels (const sTrue :: SFloatingPoint 3 3 -> SBool))
  , testCase "FP_3_4" (assert $ (== fromIntegral (count 3 4)) <$> numberOfModels (const sTrue :: SFloatingPoint 3 4 -> SBool))

  , testCase "FP_4_2" (assert $ (== fromIntegral (count 4 2)) <$> numberOfModels (const sTrue :: SFloatingPoint 4 2 -> SBool))
  , testCase "FP_4_3" (assert $ (== fromIntegral (count 4 3)) <$> numberOfModels (const sTrue :: SFloatingPoint 4 3 -> SBool))
  , testCase "FP_4_4" (assert $ (== fromIntegral (count 4 4)) <$> numberOfModels (const sTrue :: SFloatingPoint 4 4 -> SBool))

  , goldenVsStringShow "arbFp_opt_1" (optimize Lexicographic $ \x -> do {constrain (fpIsPoint x);  maximize "x" (x::SFPHalf)})
  ]

-- | Integer literals must fold in the requested direction, including both
-- tie parities and overflow. Expectations use exactly representable values.
integralConversionRounding :: Assertion
integralConversionRounding = do
  mapM_ check
    [ (0,      [0, 0, 0, 0, 0])
    , (2049,   [2048, 2050, 2050, 2048, 2048])
    , (2051,   [2052, 2052, 2052, 2050, 2050])
    , (-2049,  [-2048, -2050, -2048, -2050, -2048])
    , (-2051,  [-2052, -2052, -2050, -2052, -2050])
    , (65536,  [halfInfinity, halfInfinity, halfInfinity, 65504, 65504])
    , (-65536, [-halfInfinity, -halfInfinity, -65504, -halfInfinity, -65504])
    , (2 ^ (200 :: Int), [halfInfinity, halfInfinity, halfInfinity, 65504, 65504])
    ]
  mapM_ (\(mode, signed, unsigned) -> do
           assertEqual (show mode ++ ": signed native source") (Just signed)
             (unliteral (toSFloatingPoint (literal mode) (literal (-2049 :: Int16))) :: Maybe FPHalf)
           assertEqual (show mode ++ ": unsigned native source") (Just unsigned)
             (unliteral (toSFloatingPoint (literal mode) (literal (2049 :: Word16))) :: Maybe FPHalf))
    (zip3 modes [-2048, -2050, -2048, -2050, -2048] [2048, 2050, 2050, 2048, 2048])
 where modes = [RoundNearestTiesToEven, RoundNearestTiesToAway, RoundTowardPositive, RoundTowardNegative, RoundTowardZero]
       halfInfinity = 1 / 0 :: FPHalf

       check (sample, expected) = mapM_ (\(mode, value) ->
           assertEqual (show (sample, mode) ++ ": integer source") (Just value)
             (unliteral (toSFloatingPoint (literal mode) (literal sample :: SInteger))))
         (zip modes expected)

-- | Conversion must use the target format, not a binary64 intermediate.
-- Check a tiny nonstandard format and integer information beyond double's
-- precision, including a halfway value beyond quadruple's precision.
integralConversionWidths :: Assertion
integralConversionWidths = do
  assertEqual "tiny upward tie" (Just 10)
    (unliteral (toSFloatingPoint sRTP (9 :: SInteger)) :: Maybe (FloatingPoint 4 3))
  assertEqual "tiny downward negative tie" (Just (-10))
    (unliteral (toSFloatingPoint sRTN (-9 :: SInteger)) :: Maybe (FloatingPoint 4 3))
  let large = 2 ^ (100 :: Int) + 1
      tie   = 2 ^ (113 :: Int) + 1
  assertEqual "retain integer bits beyond binary64" (Just (fromInteger large))
    (unliteral (toSFloatingPoint sRNE (literal large :: SInteger)) :: Maybe FPQuad)
  assertEqual "quadruple upward tie" (Just (fromInteger (tie + 1)))
    (unliteral (toSFloatingPoint sRTP (literal tie :: SInteger)) :: Maybe FPQuad)

-- | Symbolic operands must still reach the solver; a symbolic rounding mode
-- must not be ignored merely because the integer operand is concrete.
symbolicIntegralConversionRounding :: Assertion
symbolicIntegralConversionRounding = do
  assertIsThm $ \mode -> (toSFloatingPoint mode (2049 :: SInteger) :: SFPHalf)
                     .== ite (mode .== sRNA .|| mode .== sRTP) 2050 2048
  assertIsThm $ \(value :: SInt16) -> value .== -2049
                                .=> (toSFloatingPoint sRTN value :: SFPHalf) .== -2050
