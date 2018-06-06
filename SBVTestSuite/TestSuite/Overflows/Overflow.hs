-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Overflows.Overflow
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for overflow checking
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Overflows.Overflow(tests) where

import Data.SBV.Tools.Overflow

import Utils.SBVTestFramework

-- Test suite
-- NB. Overflow/underflow tests are basically done by performing the operation in SInt64, and checking if the result being out-of-bounds
-- means the corresponding over/under-flow bit is raised. This has the shortcoming of not doing the proofs for the SWord64/SInt64 types,
-- since we don't have a "bigger" bit-vector type to embed it into. Mapping to SInteger is not really an option, since it generates
-- horrendous terms (instead of simple sign/zero-extension), thus making the proofs untenable.
tests :: TestTree
tests =
  testGroup "Overflows" [ testGroup "add-uf" [ testCase "w8"  $ assertIsThm $ underflow (+)   (bvAddO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ underflow (+)   (bvAddO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ underflow (+)   (bvAddO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ underflow (+)   (bvAddO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ underflow (+)   (bvAddO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ underflow (+)   (bvAddO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "add-of" [ testCase "w8"  $ assertIsThm $ overflow  (+)   (bvAddO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ overflow  (+)   (bvAddO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ overflow  (+)   (bvAddO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ overflow  (+)   (bvAddO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ overflow  (+)   (bvAddO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ overflow  (+)   (bvAddO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "sub-uf" [ testCase "w8"  $ assertIsThm $ underflow (-)   (bvSubO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ underflow (-)   (bvSubO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ underflow (-)   (bvSubO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ underflow (-)   (bvSubO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ underflow (-)   (bvSubO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ underflow (-)   (bvSubO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "sub-of" [ testCase "w8"  $ assertIsThm $ overflow  (-)   (bvSubO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ overflow  (-)   (bvSubO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ overflow  (-)   (bvSubO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ overflow  (-)   (bvSubO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ overflow  (-)   (bvSubO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ overflow  (-)   (bvSubO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "mul-uf" [ testCase "w8"  $ assertIsThm $ underflow (*)   (bvMulO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ underflow (*)   (bvMulO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ underflow (*)   (bvMulO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ underflow (*)   (bvMulO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ underflow (*)   (bvMulO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ underflow (*)   (bvMulO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "mul-of" [ testCase "w8"  $ assertIsThm $ overflow  (*)   (bvMulO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ overflow  (*)   (bvMulO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ overflow  (*)   (bvMulO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ overflow  (*)   (bvMulO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ overflow  (*)   (bvMulO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ overflow  (*)   (bvMulO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "div-uf" [ testCase "w8"  $ assertIsThm $ underflow sDiv  (bvDivO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ underflow sDiv  (bvDivO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ underflow sDiv  (bvDivO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ underflow sDiv  (bvDivO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ underflow sDiv  (bvDivO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ underflow sDiv  (bvDivO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "div-of" [ testCase "w8"  $ assertIsThm $ overflow  sDiv  (bvDivO :: SWord8  -> SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ overflow  sDiv  (bvDivO :: SWord16 -> SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ overflow  sDiv  (bvDivO :: SWord32 -> SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ overflow  sDiv  (bvDivO :: SInt8   -> SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ overflow  sDiv  (bvDivO :: SInt16  -> SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ overflow  sDiv  (bvDivO :: SInt32  -> SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "neg-uf" [ testCase "w8"  $ assertIsThm $ underflow1 (0-) (bvNegO :: SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ underflow1 (0-) (bvNegO :: SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ underflow1 (0-) (bvNegO :: SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ underflow1 (0-) (bvNegO :: SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ underflow1 (0-) (bvNegO :: SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ underflow1 (0-) (bvNegO :: SInt32  -> (SBool, SBool))
                                             ]
                        , testGroup "neg-of" [ testCase "w8"  $ assertIsThm $ overflow1  (0-) (bvNegO :: SWord8  -> (SBool, SBool))
                                             , testCase "w16" $ assertIsThm $ overflow1  (0-) (bvNegO :: SWord16 -> (SBool, SBool))
                                             , testCase "w32" $ assertIsThm $ overflow1  (0-) (bvNegO :: SWord32 -> (SBool, SBool))
                                             , testCase "i8"  $ assertIsThm $ overflow1  (0-) (bvNegO :: SInt8   -> (SBool, SBool))
                                             , testCase "i16" $ assertIsThm $ overflow1  (0-) (bvNegO :: SInt16  -> (SBool, SBool))
                                             , testCase "i32" $ assertIsThm $ overflow1  (0-) (bvNegO :: SInt32  -> (SBool, SBool))
                                             ]
                        ]


underflow :: forall a. (Integral a, Bounded a, SymWord a) => (SInt64 -> SInt64 -> SInt64) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
underflow op cond = do x  <- free "x"
                       y  <- free "y"

                       let (underflowHappens, _) = x `cond` y

                           extResult :: SInt64
                           extResult = sFromIntegral x `op` sFromIntegral y

                       return $ underflowHappens <=> extResult .< sFromIntegral (minBound :: SBV a)

overflow :: forall a. (Integral a, Bounded a, SymWord a) => (SInt64 -> SInt64 -> SInt64) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
overflow op cond = do x  <- free "x"
                      y  <- free "y"

                      let (_, overflowHappens) = x `cond` y

                          extResult :: SInt64
                          extResult = sFromIntegral x `op` sFromIntegral y

                      return $ overflowHappens <=> extResult .> sFromIntegral (maxBound :: SBV a)

underflow1 :: forall a. (Integral a, Bounded a, SymWord a) => (SInt64 -> SInt64) -> (SBV a -> (SBool, SBool)) -> Predicate
underflow1 op cond = do x  <- free "x"

                        let (underflowHappens, _) = cond x

                            extResult :: SInt64
                            extResult = op $ sFromIntegral x

                        return $ underflowHappens <=> extResult .< sFromIntegral (minBound :: SBV a)

overflow1 :: forall a. (Integral a, Bounded a, SymWord a) => (SInt64 -> SInt64) -> (SBV a -> (SBool, SBool)) -> Predicate
overflow1 op cond = do x  <- free "x"

                       let (_, overflowHappens) = cond x

                           extResult :: SInt64
                           extResult = op $ sFromIntegral x

                       return $ overflowHappens <=> extResult .> sFromIntegral (maxBound :: SBV a)
