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

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Overflows.Arithmetic(tests) where

import Data.SBV
import Data.SBV.Dynamic
import Data.SBV.Internals (unSBV, SBV(..))

import Data.SBV.Tools.Overflow

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Overflows" [testGroup "Arithmetic" ts]
  where ts = [ testGroup "add-uf" [ testCase "w8"  $ assertIsThm $ underflow  svPlus     (bvAddO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ underflow  svPlus     (bvAddO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ underflow  svPlus     (bvAddO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ underflow  svPlus     (bvAddO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ underflow  svPlus     (bvAddO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ underflow  svPlus     (bvAddO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ underflow  svPlus     (bvAddO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ underflow  svPlus     (bvAddO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "add-of" [ testCase "w8"  $ assertIsThm $ overflow   svPlus     (bvAddO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ overflow   svPlus     (bvAddO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ overflow   svPlus     (bvAddO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ overflow   svPlus     (bvAddO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ overflow   svPlus     (bvAddO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ overflow   svPlus     (bvAddO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ overflow   svPlus     (bvAddO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ overflow   svPlus     (bvAddO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "sub-uf" [ testCase "w8"  $ assertIsThm $ underflow  svMinus    (bvSubO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ underflow  svMinus    (bvSubO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ underflow  svMinus    (bvSubO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ underflow  svMinus    (bvSubO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ underflow  svMinus    (bvSubO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ underflow  svMinus    (bvSubO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ underflow  svMinus    (bvSubO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ underflow  svMinus    (bvSubO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "sub-of" [ testCase "w8"  $ assertIsThm $ overflow   svMinus    (bvSubO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ overflow   svMinus    (bvSubO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ overflow   svMinus    (bvSubO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ overflow   svMinus    (bvSubO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ overflow   svMinus    (bvSubO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ overflow   svMinus    (bvSubO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ overflow   svMinus    (bvSubO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ overflow   svMinus    (bvSubO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "mul-uf" [ testCase "w8"  $ assertIsThm $ underflow  svTimes    (bvMulO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ underflow  svTimes    (bvMulO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ underflow  svTimes    (bvMulO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ underflow  svTimes    (bvMulO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ mulChkU    bvMulOFast (bvMulO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ mulChkU    bvMulOFast (bvMulO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ mulChkU    bvMulOFast (bvMulO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ mulChkU    bvMulOFast (bvMulO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "mul-of" [ testCase "w8"  $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ mulChkO    bvMulOFast (bvMulO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "div-uf" [ testCase "w8"  $ assertIsThm $ never      svDivide    (bvDivO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ never      svDivide    (bvDivO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ never      svDivide    (bvDivO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ never      svDivide    (bvDivO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ never      svDivide    (bvDivO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ never      svDivide    (bvDivO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ never      svDivide    (bvDivO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ never      svDivide    (bvDivO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "div-of" [ testCase "w8"  $ assertIsThm $ never      svDivide    (bvDivO :: SWord8  -> SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ never      svDivide    (bvDivO :: SWord16 -> SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ never      svDivide    (bvDivO :: SWord32 -> SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ never      svDivide    (bvDivO :: SWord64 -> SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ divChk     svDivide    (bvDivO :: SInt8   -> SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ divChk     svDivide    (bvDivO :: SInt16  -> SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ divChk     svDivide    (bvDivO :: SInt32  -> SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ divChk     svDivide    (bvDivO :: SInt64  -> SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "neg-uf" [ testCase "w8"  $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ underflow1 svNeg0      (bvNegO :: SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ underflow1 svNeg0      (bvNegO :: SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ underflow1 svNeg0      (bvNegO :: SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ underflow1 svNeg0      (bvNegO :: SInt64  -> (SBool, SBool))
                                  ]
             , testGroup "neg-of" [ testCase "w8"  $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord8  -> (SBool, SBool))
                                  , testCase "w16" $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord16 -> (SBool, SBool))
                                  , testCase "w32" $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord32 -> (SBool, SBool))
                                  , testCase "w64" $ assertIsThm $ never1     svNeg0      (bvNegO :: SWord64 -> (SBool, SBool))
                                  , testCase "i8"  $ assertIsThm $ overflow1  svNeg0      (bvNegO :: SInt8   -> (SBool, SBool))
                                  , testCase "i16" $ assertIsThm $ overflow1  svNeg0      (bvNegO :: SInt16  -> (SBool, SBool))
                                  , testCase "i32" $ assertIsThm $ overflow1  svNeg0      (bvNegO :: SInt32  -> (SBool, SBool))
                                  , testCase "i64" $ assertIsThm $ overflow1  svNeg0      (bvNegO :: SInt64  -> (SBool, SBool))
                                  ]
             ]

-- 256 bits is large enough to do all these proofs
large :: Int
large = 256

type SLarge = SVal

svNeg0 :: SLarge -> SLarge
svNeg0 v = z `svMinus` v
  where z = svInteger (KBounded (hasSign v) large) 0

exactlyWhen :: SBool -> SVal -> SBool
exactlyWhen (SBV a) b = SBV $ (a `svAnd` b) `svOr` (svNot a `svAnd` svNot b)

-- Properly extend to a dynamic large vector
toLarge :: HasKind a => SBV a -> SLarge
toLarge v
  | extra < 0 = error $ "toLarge: Unexpected size: " ++ show (n, large)
  | hasSign v = p `svJoin` dv
  | True      = z `svJoin` dv
  where n     = intSizeOf v
        extra = large - n

        dv    = unSBV v
        mk    = svInteger (KBounded True extra)
        z     = mk 0
        o     = mk (-1)
        pos   = (dv `svTestBit` (n-1)) `svEqual` svFalse
        p     = svIte pos z o

-- Multiplication checks are expensive. For these, we simply check that the SBV encodings and the z3 versions are equivalent
mulChkO :: forall a. SymVal a => (SBV a -> SBV a -> (SBool, SBool)) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
mulChkO fast slow = do setLogic Logic_NONE
                       x <- free "x"
                       y <- free "y"

                       let (_, ov1) = x `fast` y
                           (_, ov2) = x `slow` y

                       return $ ov1 .== ov2

-- Underflow mults
mulChkU :: forall a. SymVal a => (SBV a -> SBV a -> (SBool, SBool)) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
mulChkU fast slow = do setLogic Logic_NONE
                       x <- free "x"
                       y <- free "y"

                       let (uf1, _) = x `fast` y
                           (uf2, _) = x `slow` y

                       return $ uf1 .== uf2

-- Signed division can only underflow under one condition, check that simply instead of trying to do an expensive embedding proof
divChk :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge -> SLarge) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
divChk _op cond = do x  <- free "x"
                     y  <- free "y"

                     let (_, overflowHappens) = x `cond` y

                         special = (unSBV x `svEqual` topSet) `svAnd` (unSBV y `svEqual` neg1)

                         n      = intSizeOf x
                         neg1   = svInteger (KBounded True n) (-1)
                         topSet = svInteger (KBounded True n) (2^(n-1))

                     return $ overflowHappens `exactlyWhen` special

-- For a few cases, we expect them to "never" overflow. The "embedding proofs" are either too expensive (in case of division), or
-- not possible (in case of negation). We capture these here.
never :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge -> SLarge) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
never _op cond = do x  <- free "x"
                    y  <- free "y"

                    let (underflowHappens, _) = x `cond` y

                    return $ underflowHappens `exactlyWhen` svFalse

never1 :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge) -> (SBV a -> (SBool, SBool)) -> Predicate
never1 _op cond = do x  <- free "x"

                     let (underflowHappens, _) = cond x

                     return $ underflowHappens `exactlyWhen` svFalse

underflow :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge -> SLarge) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
underflow op cond = do x  <- free "x"
                       y  <- free "y"

                       let (underflowHappens, _) = x `cond` y

                           extResult :: SLarge
                           extResult = toLarge x `op` toLarge y


                       return $ underflowHappens `exactlyWhen` (extResult `svLessThan` toLarge (minBound :: SBV a))

overflow :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge -> SLarge) -> (SBV a -> SBV a -> (SBool, SBool)) -> Predicate
overflow op cond = do x  <- free "x"
                      y  <- free "y"

                      let (_, overflowHappens) = x `cond` y

                          extResult :: SLarge
                          extResult = toLarge x `op` toLarge y

                      return $ overflowHappens `exactlyWhen` (extResult `svGreaterThan` toLarge (maxBound :: SBV a))

underflow1 :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge) -> (SBV a -> (SBool, SBool)) -> Predicate
underflow1 op cond = do x  <- free "x"

                        let (underflowHappens, _) = cond x

                            extResult :: SLarge
                            extResult = op $ toLarge x

                        return $ underflowHappens `exactlyWhen` (extResult `svLessThan` toLarge (minBound :: SBV a))

overflow1 :: forall a. (Integral a, Bounded a, SymVal a) => (SLarge -> SLarge) -> (SBV a -> (SBool, SBool)) -> Predicate
overflow1 op cond = do x  <- free "x"

                       let (_, overflowHappens) = cond x

                           extResult :: SLarge
                           extResult = op $ toLarge x

                       return $ overflowHappens `exactlyWhen` (extResult `svGreaterThan` toLarge (maxBound :: SBV a))

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
