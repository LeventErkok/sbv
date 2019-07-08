-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.QuickCheck.QC
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Quick-check based test suite for SBV
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.QuickCheck.QC (tests) where

import Utils.SBVTestFramework

unaryArith :: String -> (forall a. Num a => a -> a) -> [TestTree]
unaryArith nm op =  qc1 (nm ++ ".SWord8"  ) op (op :: SWord8   -> SWord8)
                 ++ qc1 (nm ++ ".SWord16" ) op (op :: SWord16  -> SWord16)
                 ++ qc1 (nm ++ ".SWord32" ) op (op :: SWord32  -> SWord32)
                 ++ qc1 (nm ++ ".SWord64" ) op (op :: SWord64  -> SWord64)
                 ++ qc1 (nm ++ ".SInt8"   ) op (op :: SInt8    -> SInt8)
                 ++ qc1 (nm ++ ".SInt16"  ) op (op :: SInt16   -> SInt16)
                 ++ qc1 (nm ++ ".SInt32"  ) op (op :: SInt32   -> SInt32)
                 ++ qc1 (nm ++ ".SInt64"  ) op (op :: SInt64   -> SInt64)
                 ++ qc1 (nm ++ ".SInteger") op (op :: SInteger -> SInteger)
                 ++ qc1 (nm ++ ".SReal"   ) op (op :: SReal    -> SReal)
                 ++ qc1 (nm ++ ".SFloat"  ) op (op :: SFloat   -> SFloat)
                 ++ qc1 (nm ++ ".SDouble" ) op (op :: SDouble  -> SDouble)

binaryArith :: String -> (forall a. Num a => a -> a -> a) -> [TestTree]
binaryArith nm op = qc2 (nm ++ ".SWord8"  ) op (op :: SWord8   -> SWord8   -> SWord8)
                 ++ qc2 (nm ++ ".SWord16" ) op (op :: SWord16  -> SWord16  -> SWord16)
                 ++ qc2 (nm ++ ".SWord32" ) op (op :: SWord32  -> SWord32  -> SWord32)
                 ++ qc2 (nm ++ ".SWord64" ) op (op :: SWord64  -> SWord64  -> SWord64)
                 ++ qc2 (nm ++ ".SInt8"   ) op (op :: SInt8    -> SInt8    -> SInt8)
                 ++ qc2 (nm ++ ".SInt16"  ) op (op :: SInt16   -> SInt16   -> SInt16)
                 ++ qc2 (nm ++ ".SInt32"  ) op (op :: SInt32   -> SInt32   -> SInt32)
                 ++ qc2 (nm ++ ".SInt64"  ) op (op :: SInt64   -> SInt64   -> SInt64)
                 ++ qc2 (nm ++ ".SInteger") op (op :: SInteger -> SInteger -> SInteger)
                 ++ qc2 (nm ++ ".SReal"   ) op (op :: SReal    -> SReal    -> SReal)
                 ++ qc2 (nm ++ ".SFloat"  ) op (op :: SFloat   -> SFloat   -> SFloat)
                 ++ qc2 (nm ++ ".SDouble" ) op (op :: SDouble  -> SDouble  -> SDouble)

-- Test suite
tests :: TestTree
tests = testGroup "QuickCheck.QC" [
            testGroup "Arithmetic" [
                 testGroup "Unary"  $    unaryArith "negate" negate
                                      ++ unaryArith "abs"    abs
                                      ++ unaryArith "signum" signum
               , testGroup "Binary" $    binaryArith "+"     (+)
                                      ++ binaryArith "-"     (-)
                                      ++ binaryArith "*"     (*)
               ]
        ]
