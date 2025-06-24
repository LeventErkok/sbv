-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Overflows.Arithmetic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for overflow checking
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Overflows.Arithmetic(tests) where

import Data.SBV
import Data.SBV.Dynamic
import Data.SBV.Internals (unSBV, SBV(..), SymVal(minMaxBound))

import Data.SBV.Tools.Overflow

import Data.Proxy
import GHC.TypeLits

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Overflows" [testGroup "Arithmetic" ts]
  where ts = [ testGroup "add-ov" [ testCase "w8"  $ assertIsThm $ overflow  svPlus   (bvAddO :: SWord8  -> SWord8  -> SBool)
                                  , testCase "w16" $ assertIsThm $ overflow  svPlus   (bvAddO :: SWord16 -> SWord16 -> SBool)
                                  , testCase "w32" $ assertIsThm $ overflow  svPlus   (bvAddO :: SWord32 -> SWord32 -> SBool)
                                  , testCase "w64" $ assertIsThm $ overflow  svPlus   (bvAddO :: SWord64 -> SWord64 -> SBool)
                                  , testCase "i8"  $ assertIsThm $ overflow  svPlus   (bvAddO :: SInt8   -> SInt8   -> SBool)
                                  , testCase "i16" $ assertIsThm $ overflow  svPlus   (bvAddO :: SInt16  -> SInt16  -> SBool)
                                  , testCase "i32" $ assertIsThm $ overflow  svPlus   (bvAddO :: SInt32  -> SInt32  -> SBool)
                                  , testCase "i64" $ assertIsThm $ overflow  svPlus   (bvAddO :: SInt64  -> SInt64  -> SBool)
                                  ]

             , testGroup "sub-ov" [ testCase "w8"  $ assertIsThm $ overflow  svMinus  (bvSubO :: SWord8  -> SWord8  -> SBool)
                                  , testCase "w16" $ assertIsThm $ overflow  svMinus  (bvSubO :: SWord16 -> SWord16 -> SBool)
                                  , testCase "w32" $ assertIsThm $ overflow  svMinus  (bvSubO :: SWord32 -> SWord32 -> SBool)
                                  , testCase "w64" $ assertIsThm $ overflow  svMinus  (bvSubO :: SWord64 -> SWord64 -> SBool)
                                  , testCase "i8"  $ assertIsThm $ overflow  svMinus  (bvSubO :: SInt8   -> SInt8   -> SBool)
                                  , testCase "i16" $ assertIsThm $ overflow  svMinus  (bvSubO :: SInt16  -> SInt16  -> SBool)
                                  , testCase "i32" $ assertIsThm $ overflow  svMinus  (bvSubO :: SInt32  -> SInt32  -> SBool)
                                  , testCase "i64" $ assertIsThm $ overflow  svMinus  (bvSubO :: SInt64  -> SInt64  -> SBool)
                                  ]

             -- Multiplication checks are expensive for z3; so only do at a few instances with z3
             , testGroup "mul-ov" [ testCase "w8"  $ assertIsThm $ overflow  svTimes  (bvMulO :: SWord8  -> SWord8  -> SBool)
                                  , testCase "w16" $ assertIsThm $ overflow  svTimes  (bvMulO :: SWord16 -> SWord16 -> SBool)
                                  -- , testCase "w32" $ assertIsThm $ overflow  svTimes  (bvMulO :: SWord32 -> SWord32 -> SBool)
                                  -- , testCase "w64" $ assertIsThm $ overflow  svTimes  (bvMulO :: SWord64 -> SWord64 -> SBool)
                                  , testCase "i8"  $ assertIsThm $ overflow  svTimes  (bvMulO :: SInt8   -> SInt8   -> SBool)
                                  -- , testCase "i16" $ assertIsThm $ overflow  svTimes  (bvMulO :: SInt16  -> SInt16  -> SBool)
                                  -- , testCase "i32" $ assertIsThm $ overflow  svTimes  (bvMulO :: SInt32  -> SInt32  -> SBool)
                                  -- , testCase "i64" $ assertIsThm $ overflow  svTimes  (bvMulO :: SInt64  -> SInt64  -> SBool)
                                  ]

             -- Another group of multiplication overflow tests for signed-multiplication, using bitwuzla
             , testGroup "mul-special"
                                 [ testCase "smov1_int"  $ assert $ smulCheck (Proxy @1)  True
                                 , testCase "smov1_txt"  $ assert $ smulCheck (Proxy @1)  False
                                 , testCase "smov2_int"  $ assert $ smulCheck (Proxy @2)  True
                                 , testCase "smov2_txt"  $ assert $ smulCheck (Proxy @2)  False
                                 , testCase "smov3_int"  $ assert $ smulCheck (Proxy @3)  True
                                 , testCase "smov3_txt"  $ assert $ smulCheck (Proxy @3)  False
                                 , testCase "smov4_int"  $ assert $ smulCheck (Proxy @4)  True
                                 , testCase "smov4_txt"  $ assert $ smulCheck (Proxy @4)  False
                                 , testCase "smov5_int"  $ assert $ smulCheck (Proxy @5)  True
                                 , testCase "smov5_txt"  $ assert $ smulCheck (Proxy @5)  False
                                 , testCase "smov6_int"  $ assert $ smulCheck (Proxy @6)  True
                                 , testCase "smov6_txt"  $ assert $ smulCheck (Proxy @6)  False
                                 , testCase "smov7_int"  $ assert $ smulCheck (Proxy @7)  True
                                 , testCase "smov7_txt"  $ assert $ smulCheck (Proxy @7)  False
                                 , testCase "smov8_int"  $ assert $ smulCheck (Proxy @8)  True
                                 , testCase "smov8_txt"  $ assert $ smulCheck (Proxy @8)  False
                                 -- After this, text-book checks take long; so we just check against internal
                                 , testCase "smov24_int" $ assert $ smulCheck (Proxy @24) True
                                 , testCase "smov32_int" $ assert $ smulCheck (Proxy @32) True
                                 , testCase "smov64_int" $ assert $ smulCheck (Proxy @64) True
                                 ]

             , testGroup "div-ov" [ testCase "w8"  $ assertIsThm $ never     svDivide (bvDivO :: SWord8  -> SWord8  -> SBool)
                                  , testCase "w16" $ assertIsThm $ never     svDivide (bvDivO :: SWord16 -> SWord16 -> SBool)
                                  , testCase "w32" $ assertIsThm $ never     svDivide (bvDivO :: SWord32 -> SWord32 -> SBool)
                                  , testCase "w64" $ assertIsThm $ never     svDivide (bvDivO :: SWord64 -> SWord64 -> SBool)
                                  , testCase "i8"  $ assertIsThm $ overflow  svDivide (bvDivO :: SInt8   -> SInt8   -> SBool)
                                  , testCase "i16" $ assertIsThm $ overflow  svDivide (bvDivO :: SInt16  -> SInt16  -> SBool)
                                  , testCase "i32" $ assertIsThm $ overflow  svDivide (bvDivO :: SInt32  -> SInt32  -> SBool)
                                  , testCase "i64" $ assertIsThm $ overflow  svDivide (bvDivO :: SInt64  -> SInt64  -> SBool)
                                  ]

             , testGroup "neg-ov" [ testCase "w8"  $ assertIsThm $ never1    svNeg0   (bvNegO :: SWord8  -> SBool)
                                  , testCase "w16" $ assertIsThm $ never1    svNeg0   (bvNegO :: SWord16 -> SBool)
                                  , testCase "w32" $ assertIsThm $ never1    svNeg0   (bvNegO :: SWord32 -> SBool)
                                  , testCase "w64" $ assertIsThm $ never1    svNeg0   (bvNegO :: SWord64 -> SBool)
                                  , testCase "i8"  $ assertIsThm $ overflow1 svNeg0   (bvNegO :: SInt8   -> SBool)
                                  , testCase "i16" $ assertIsThm $ overflow1 svNeg0   (bvNegO :: SInt16  -> SBool)
                                  , testCase "i32" $ assertIsThm $ overflow1 svNeg0   (bvNegO :: SInt32  -> SBool)
                                  , testCase "i64" $ assertIsThm $ overflow1 svNeg0   (bvNegO :: SInt64  -> SBool)
                                  ]
             ]

-- 128 bits is large enough to do all these proofs
large :: Int
large = 128

type SLarge = SVal

svNeg0 :: SLarge -> SLarge
svNeg0 v = z `svMinus` v
  where z = svInteger (KBounded (hasSign v) large) 0

exactlyWhen :: SBool -> SVal -> SBool
exactlyWhen (SBV a) b = SBV $ (a `svAnd` b) `svOr` (svNot a `svAnd` svNot b)

-- Properly extend to a dynamic signed large vector. This works because we grow to 256 bits, which is high enough.
toLarge :: HasKind a => SBV a -> SLarge
toLarge v
  | extra < 0 = error $ "toLarge: Unexpected size: " ++ show (n, large)
  | hasSign v =            svSignExtend extra (unSBV v)
  | True      = mkSigned $ svZeroExtend extra (unSBV v)
  where n     = intSizeOf v
        extra = large - n

        mkSigned = svFromIntegral (KBounded True large)

-- For a few cases, we expect them to "never" overflow. The "embedding proofs" are either too expensive (in case of division), or
-- not possible (in case of negation). We capture these here.
never :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge -> SLarge) -> (SBV a -> SBV a -> SBool) -> Predicate
never _op cond = do x  <- free "x"
                    y  <- free "y"

                    let overFlowHappens = x `cond` y

                    return $ overFlowHappens `exactlyWhen` svFalse

never1 :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge) -> (SBV a -> SBool) -> Predicate
never1 _op cond = do x  <- free "x"

                     let overflowHappens = cond x

                     return $ overflowHappens `exactlyWhen` svFalse

overflow :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge -> SLarge) -> (SBV a -> SBV a -> SBool) -> Predicate
overflow op cond = do x  <- free "x"
                      y  <- free "y"

                      let overflowHappens = x `cond` y

                          extResult :: SLarge
                          extResult = toLarge x `op` toLarge y

                          minb, maxb :: a
                          (minb, maxb) = case minMaxBound of
                                           Nothing -> error "overflow on type that doesn't support bounded"
                                           Just ab -> ab

                      return $ overflowHappens `exactlyWhen` (      (extResult `svGreaterThan` toLarge (literal maxb))
                                                             `svOr` (extResult `svLessThan`    toLarge (literal minb))
                                                             )

overflow1 :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge) -> (SBV a -> SBool) -> Predicate
overflow1 op cond = do x  <- free "x"

                       let overflowHappens = cond x

                           extResult :: SLarge
                           extResult = op $ toLarge x

                           minb, maxb :: a
                           (minb, maxb) = case minMaxBound of
                                            Nothing -> error "overflow on type that doesn't support bounded"
                                            Just ab -> ab

                       return $ overflowHappens `exactlyWhen` (       (extResult `svGreaterThan` toLarge (literal maxb))
                                                               `svOr` (extResult `svLessThan`    toLarge (literal minb)))

-- Custom checker for signedMulOverflow
smulCheck :: forall proxy n. ( KnownNat n,          BVIsNonZero n
                             , KnownNat (n+1),      BVIsNonZero (n+1)
                             , KnownNat (n+n),      BVIsNonZero (n+n)
                             , KnownNat (2+Log2 n), BVIsNonZero (2+Log2 n)
                             ) => proxy n -> Bool -> IO Bool
smulCheck _ builtin = check (if builtin then bvMulO else textbook)
   where check f = isTheoremWith bitwuzla $ do
                        x <- sInt "x"
                        y <- sInt "y"
                        pure $ f x y .== (signedMulOverflow :: SInt n -> SInt n -> SBool) x y

         textbook x y = prod2N ./= sFromIntegral prodN
           where prod2N :: SInt (n+n)
                 prod2N = sFromIntegral x * sFromIntegral y

                 prodN :: SInt n
                 prodN = x * y

{- HLint ignore module "Reduce duplication" -}
