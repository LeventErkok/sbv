-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.Floats
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test-suite for generating floating-point related C code
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.Floats(tests) where

import Data.SBV.Internals

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CodeGeneration.Floats" [
   goldenVsStringShow "floats_cgen" code
 ]
 where code  = thd <$> compileToCLib' "floatCodeGen" cases

       thd (_, _, r) = r

       setup = do cgSRealType CgLongDouble
                  cgIntegerSize 64
                  cgSetDriverValues [42, 43, 44]

       test1 nm f = (nm, do setup
                            a <- cgInput "a"
                            cgReturn (f a))

       test2 nm f = (nm, do setup
                            a <- cgInput "a"
                            b <- cgInput "b"
                            cgReturn (f a b))

       test3 nm f = (nm, do setup
                            a <- cgInput "a"
                            b <- cgInput "b"
                            c <- cgInput "c"
                            cgReturn (f a b c))

       cases = [
            test1 "toFP_Int8_ToFloat"       (toSFloat sRoundNearestTiesToEven  :: SInt8    -> SFloat)
          , test1 "toFP_Int16_ToFloat"      (toSFloat sRoundNearestTiesToEven  :: SInt16   -> SFloat)
          , test1 "toFP_Int32_ToFloat"      (toSFloat sRoundNearestTiesToEven  :: SInt32   -> SFloat)
          , test1 "toFP_Int64_ToFloat"      (toSFloat sRoundNearestTiesToEven  :: SInt64   -> SFloat)
          , test1 "toFP_Word8_ToFloat"      (toSFloat sRoundNearestTiesToEven  :: SWord8   -> SFloat)
          , test1 "toFP_Word16_ToFloat"     (toSFloat sRoundNearestTiesToEven  :: SWord16  -> SFloat)
          , test1 "toFP_Word32_ToFloat"     (toSFloat sRoundNearestTiesToEven  :: SWord32  -> SFloat)
          , test1 "toFP_Word64_ToFloat"     (toSFloat sRoundNearestTiesToEven  :: SWord64  -> SFloat)
          , test1 "toFP_Float_ToFloat"      (toSFloat sRoundNearestTiesToEven  :: SFloat   -> SFloat)
          , test1 "toFP_Double_ToFloat"     (toSFloat sRoundNearestTiesToEven  :: SDouble  -> SFloat)
          , test1 "toFP_Integer_ToFloat"    (toSFloat sRoundNearestTiesToEven  :: SInteger -> SFloat)
          , test1 "toFP_Real_ToFloat"       (toSFloat sRoundNearestTiesToEven  :: SReal    -> SFloat)

          , test1 "toFP_Int8_ToDouble"      (toSDouble sRoundNearestTiesToEven :: SInt8    -> SDouble)
          , test1 "toFP_Int16_ToDouble"     (toSDouble sRoundNearestTiesToEven :: SInt16   -> SDouble)
          , test1 "toFP_Int32_ToDouble"     (toSDouble sRoundNearestTiesToEven :: SInt32   -> SDouble)
          , test1 "toFP_Int64_ToDouble"     (toSDouble sRoundNearestTiesToEven :: SInt64   -> SDouble)
          , test1 "toFP_Word8_ToDouble"     (toSDouble sRoundNearestTiesToEven :: SWord8   -> SDouble)
          , test1 "toFP_Word16_ToDouble"    (toSDouble sRoundNearestTiesToEven :: SWord16  -> SDouble)
          , test1 "toFP_Word32_ToDouble"    (toSDouble sRoundNearestTiesToEven :: SWord32  -> SDouble)
          , test1 "toFP_Word64_ToDouble"    (toSDouble sRoundNearestTiesToEven :: SWord64  -> SDouble)
          , test1 "toFP_Float_ToDouble"     (toSDouble sRoundNearestTiesToEven :: SFloat   -> SDouble)
          , test1 "toFP_Double_ToDouble"    (toSDouble sRoundNearestTiesToEven :: SDouble  -> SDouble)
          , test1 "toFP_Integer_ToDouble"   (toSDouble sRoundNearestTiesToEven :: SInteger -> SDouble)
          , test1 "toFP_Real_ToDouble"      (toSDouble sRoundNearestTiesToEven :: SReal    -> SDouble)

          , test1 "fromFP_Float_ToInt8"     (fromSFloat sRoundNearestTiesToEven :: SFloat -> SInt8)
          , test1 "fromFP_Float_ToInt16"    (fromSFloat sRoundNearestTiesToEven :: SFloat -> SInt16)
          , test1 "fromFP_Float_ToInt32"    (fromSFloat sRoundNearestTiesToEven :: SFloat -> SInt32)
          , test1 "fromFP_Float_ToInt64"    (fromSFloat sRoundNearestTiesToEven :: SFloat -> SInt64)
          , test1 "fromFP_Float_ToWord8"    (fromSFloat sRoundNearestTiesToEven :: SFloat -> SWord8)
          , test1 "fromFP_Float_ToWord16"   (fromSFloat sRoundNearestTiesToEven :: SFloat -> SWord16)
          , test1 "fromFP_Float_ToWord32"   (fromSFloat sRoundNearestTiesToEven :: SFloat -> SWord32)
          , test1 "fromFP_Float_ToWord64"   (fromSFloat sRoundNearestTiesToEven :: SFloat -> SWord64)
          , test1 "fromFP_Float_ToFloat"    (fromSFloat sRoundNearestTiesToEven :: SFloat -> SFloat)
          , test1 "fromFP_Float_ToDouble"   (fromSFloat sRoundNearestTiesToEven :: SFloat -> SDouble)
          , test1 "fromFP_Float_ToInteger"  (fromSFloat sRoundNearestTiesToEven :: SFloat -> SInteger)
          , test1 "fromFP_Float_ToReal"     (fromSFloat sRoundNearestTiesToEven :: SFloat -> SReal)

          , test1 "fromFP_DoubleTo_Int8"    (fromSDouble sRoundNearestTiesToEven :: SDouble -> SInt8)
          , test1 "fromFP_DoubleTo_Int16"   (fromSDouble sRoundNearestTiesToEven :: SDouble -> SInt16)
          , test1 "fromFP_DoubleTo_Int32"   (fromSDouble sRoundNearestTiesToEven :: SDouble -> SInt32)
          , test1 "fromFP_DoubleTo_Int64"   (fromSDouble sRoundNearestTiesToEven :: SDouble -> SInt64)
          , test1 "fromFP_DoubleTo_Word8"   (fromSDouble sRoundNearestTiesToEven :: SDouble -> SWord8)
          , test1 "fromFP_DoubleTo_Word16"  (fromSDouble sRoundNearestTiesToEven :: SDouble -> SWord16)
          , test1 "fromFP_DoubleTo_Word32"  (fromSDouble sRoundNearestTiesToEven :: SDouble -> SWord32)
          , test1 "fromFP_DoubleTo_Word64"  (fromSDouble sRoundNearestTiesToEven :: SDouble -> SWord64)
          , test1 "fromFP_DoubleTo_Float"   (fromSDouble sRoundNearestTiesToEven :: SDouble -> SFloat)
          , test1 "fromFP_DoubleTo_Double"  (fromSDouble sRoundNearestTiesToEven :: SDouble -> SDouble)
          , test1 "fromFP_DoubleTo_Integer" (fromSDouble sRoundNearestTiesToEven :: SDouble -> SInteger)
          , test1 "fromFP_DoubleTo_Real"    (fromSDouble sRoundNearestTiesToEven :: SDouble -> SReal)

          , test1 "fromFP_SWord32_SFloat"   (sWord32AsSFloat  :: SWord32 -> SFloat)
          , test1 "fromFP_SWord64_SDouble"  (sWord64AsSDouble :: SWord64 -> SDouble)
          , test1 "fromFP_SFloat_SWord32"   (sFloatAsSWord32  :: SFloat  -> SWord32)
          , test1 "fromFP_SDouble_SWord64"  (sDoubleAsSWord64 :: SDouble -> SWord64)

          , test1 "f_FP_Abs"                (abs    :: SFloat -> SFloat)
          , test1 "d_FP_Abs"                (abs    :: SDouble -> SDouble)

          , test1 "f_FP_Neg"                (negate :: SFloat -> SFloat)
          , test1 "d_FP_Neg"                (negate :: SDouble -> SDouble)

          , test2 "f_FP_Add"                (fpAdd  sRoundNearestTiesToEven :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Add"                (fpAdd  sRoundNearestTiesToEven :: SDouble -> SDouble -> SDouble)

          , test2 "f_FP_Sub"                (fpSub  sRoundNearestTiesToEven :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Sub"                (fpSub  sRoundNearestTiesToEven :: SDouble -> SDouble -> SDouble)

          , test2 "f_FP_Mul"                (fpMul  sRoundNearestTiesToEven :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Mul"                (fpMul  sRoundNearestTiesToEven :: SDouble -> SDouble -> SDouble)

          , test2 "f_FP_Div"                (fpDiv  sRoundNearestTiesToEven :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Div"                (fpDiv  sRoundNearestTiesToEven :: SDouble -> SDouble -> SDouble)

          , test3 "f_FP_FMA"                (fpFMA  sRoundNearestTiesToEven :: SFloat  -> SFloat  -> SFloat  -> SFloat)
          , test3 "d_FP_FMA"                (fpFMA  sRoundNearestTiesToEven :: SDouble -> SDouble -> SDouble -> SDouble)

          , test1 "f_FP_Sqrt"               (fpSqrt sRoundNearestTiesToEven :: SFloat  -> SFloat)
          , test1 "d_FP_Sqrt"               (fpSqrt sRoundNearestTiesToEven :: SDouble -> SDouble)

          , test2 "f_FP_Rem"                (fpRem  :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Rem"                (fpRem  :: SDouble -> SDouble -> SDouble)

          , test1 "f_FP_RoundToIntegral"    (fpRoundToIntegral sRoundNearestTiesToEven :: SFloat  -> SFloat)
          , test1 "d_FP_RoundToIntegral"    (fpRoundToIntegral sRoundNearestTiesToEven :: SDouble -> SDouble)

          , test2 "f_FP_Min"                (fpMin :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Min"                (fpMin :: SDouble -> SDouble -> SDouble)

          , test2 "f_FP_Max"                (fpMax :: SFloat  -> SFloat  -> SFloat)
          , test2 "d_FP_Max"                (fpMax :: SDouble -> SDouble -> SDouble)

          , test2 "f_FP_IsEqualObject"      (fpIsEqualObject :: SFloat  -> SFloat  -> SBool)
          , test2 "d_FP_IsEqualObject"      (fpIsEqualObject :: SDouble -> SDouble -> SBool)

          , test1 "f_FP_IsNormal"           (fpIsNormal :: SFloat  -> SBool)
          , test1 "d_FP_IsNormal"           (fpIsNormal :: SDouble -> SBool)

          , test1 "f_FP_IsZero"             (fpIsZero :: SFloat  -> SBool)
          , test1 "d_FP_IsZero"             (fpIsZero :: SDouble -> SBool)

          , test1 "f_FP_IsSubnormal"        (fpIsSubnormal :: SFloat  -> SBool)
          , test1 "d_FP_IsSubnormal"        (fpIsSubnormal :: SDouble -> SBool)

          , test1 "f_FP_IsInfinite"         (fpIsInfinite :: SFloat  -> SBool)
          , test1 "d_FP_IsInfinite"         (fpIsInfinite :: SDouble -> SBool)

          , test1 "f_FP_IsNaN"              (fpIsNaN :: SFloat  -> SBool)
          , test1 "d_FP_IsNaN"              (fpIsNaN :: SDouble -> SBool)

          , test1 "f_FP_IsNegative"         (fpIsNegative :: SFloat  -> SBool)
          , test1 "d_FP_IsNegative"         (fpIsNegative :: SDouble -> SBool)

          , test1 "f_FP_IsPositive"         (fpIsPositive :: SFloat  -> SBool)
          , test1 "d_FP_IsPositive"         (fpIsPositive :: SDouble -> SBool)
          ]

{- HLint ignore module "Reduce duplication" -}
