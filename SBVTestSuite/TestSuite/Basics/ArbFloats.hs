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
import Control.Monad (forM, forM_)
import Data.SBV.Control

-- | Number of inhabitants: @2^sb(2^eb - 1) + 3@.
count :: Integer -> Integer -> Integer
count eb sb = 2^sb * (2^eb - 1) + 3

-- | Concrete and symbolic arbitrary-format floating-point checks.
tests :: TestTree
tests = testGroup "Basics.ArbFloats"
  [ testCase "integral conversion rounding" integralConversionRounding
  , testCase "integral conversion format widths" integralConversionWidths
  , testCase "symbolic integral conversion rounding" symbolicIntegralConversionRounding
  , testCase "native integral conversion rounding" nativeIntegralConversionRounding
  , testCase "native integral conversion solver agreement" nativeIntegralConversionAgreement
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

-- | Check both native target formats at ties of either parity, with both
-- signs and directed overflow. All expectations are exactly representable.
nativeIntegralConversionRounding :: Assertion
nativeIntegralConversionRounding = do
  check (toSFloat, 24, 128)
  check (toSDouble, 53, 1024)
  source (literal (-127)              :: SInt8)
  source (literal (-32767)            :: SInt16)
  source (literal (-16777217)         :: SInt32)
  source (literal (-9007199254740993) :: SInt64)
  source (literal 255                 :: SWord8)
  source (literal 65535               :: SWord16)
  source (literal 16777217            :: SWord32)
  source (literal 9007199254740993    :: SWord64)
 where check :: (RealFloat a, SymVal a, Show a) => (SRoundingMode -> SInteger -> SBV a, Int, Int) -> Assertion
       check (convert, precision, exponentLimit) = do
         let base           = 2 ^ precision :: Integer
             number         = fromInteger
             nativeInfinity = 1 / 0
             largest        = number ((2 ^ precision - 1) * 2 ^ (exponentLimit - precision))
             cases = [ (0, [0, 0, 0, 0, 0])
                     , (base + 1, map number [base, base + 2, base + 2, base, base])
                     , (base + 3, map number [base + 4, base + 4, base + 4, base + 2, base + 2])
                     , (negate (base + 1), map (negate . number) [base, base + 2, base, base + 2, base])
                     , (negate (base + 3), map (negate . number) [base + 4, base + 4, base + 2, base + 4, base + 2])
                     , (2 ^ exponentLimit, [nativeInfinity, nativeInfinity, nativeInfinity, largest, largest])
                     , (negate (2 ^ exponentLimit), [-nativeInfinity, -nativeInfinity, -largest, -nativeInfinity, -largest])
                     , (2 ^ (exponentLimit + 200), [nativeInfinity, nativeInfinity, nativeInfinity, largest, largest])
                     ]
         forM_ cases $ \(sample, expected) ->
           forM_ (zip [minBound .. maxBound] expected) $ \(mode, value) ->
             assertEqual (show (precision, sample, mode)) (Just value) (unliteral (convert (literal mode) (literal sample)))
         forM_ [sRNE, sRNA, sRTP, sRTN, sRTZ] $ \mode ->
           assertEqual "Integer zero stays positive" (Just False) (isNegativeZero <$> unliteral (convert mode 0))

       source :: (Integral a, IEEEFloatConvertible a) => SBV a -> Assertion
       source value = forM_ [minBound .. maxBound] $ \mode -> do
         let integer = literal (maybe (error "Expected a literal source") toInteger (unliteral value)) :: SInteger
             rm      = literal mode
         assertEqual "Native source to Float"  (unliteral (toSFloat  rm integer)) (unliteral (toSFloat  rm value))
         assertEqual "Native source to Double" (unliteral (toSDouble rm integer)) (unliteral (toSDouble rm value))

-- | Compare native folding with solver casts, keeping both the integer and
-- rounding mode symbolic. Include near-ties that exceed binary64 precision
-- to detect accidental rounding through Double on the way to Float.
nativeIntegralConversionAgreement :: Assertion
nativeIntegralConversionAgreement = do
  observations <- runSMT $ do
    input <- sInteger "input"
    mode  <- free "mode"
    query $ forM [(n, rm) | n <- samples, rm <- [minBound .. maxBound]] $ \(n, rm) -> inNewAssertionStack $ do
      constrain (input .== literal n)
      constrain (mode .== literal rm)
      status <- checkSat
      case status of
        Sat -> do f <- getValue (toSFloat mode input)
                  d <- getValue (toSDouble mode input)
                  pure (n, rm, status, Just f, Just d)
        _   -> pure (n, rm, status, Nothing, Nothing)
  forM_ observations $ \(n, rm, status, f, d) -> do
    assertEqual "Concrete input and rounding mode are satisfiable" Sat status
    assertEqual (show (n, rm) ++ ": Float")  f (unliteral (toSFloat  (literal rm) (literal n :: SInteger)))
    assertEqual (show (n, rm) ++ ": Double") d (unliteral (toSDouble (literal rm) (literal n :: SInteger)))
  assertIsThm $ \mode -> toSFloat mode (16777217 :: SInteger)
                     .== ite (mode .== sRNA .|| mode .== sRTP) 16777218 16777216
  assertIsThm $ \mode -> toSDouble mode (-9007199254740993 :: SInteger)
                     .== ite (mode .== sRNA .|| mode .== sRTN) (-9007199254740994) (-9007199254740992)
 where samples = 0 : [sign * n | sign <- [1, -1], n <- [2 ^ (24 :: Int) + 1, 2 ^ (24 :: Int) + 3,
                                                      2 ^ (53 :: Int) + 1, 2 ^ (53 :: Int) + 3,
                                                      2 ^ (54 :: Int) + 2 ^ (30 :: Int) + 1,
                                                      2 ^ (128 :: Int), 2 ^ (1024 :: Int)]]
