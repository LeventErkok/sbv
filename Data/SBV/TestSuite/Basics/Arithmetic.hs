-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Basics.Arithmetic
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for basic concrete arithmetic
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}

module Data.SBV.TestSuite.Basics.Arithmetic(testSuite) where

import Data.SBV
import Data.SBV.Internals

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test $
        genBinTest "+"                (+)
     ++ genBinTest "-"                (-)
     ++ genBinTest "*"                (*)
     ++ genUnTest  "negate"           negate
     ++ genUnTest  "abs"              abs
     ++ genUnTest  "signum"           signum
     ++ genBinTest ".&."              (.&.)
     ++ genBinTest ".|."              (.|.)
     ++ genBinTest "xor"              (xor)
     ++ genUnTest  "complement"       complement
     ++ genIntTest "shift"            shift
     ++ genIntTest "rotate"           rotate
     ++ genIntTest "setBit"           setBit
     ++ genIntTest "clearBit"         clearBit
     ++ genIntTest "complementBit"    complementBit
     ++ genIntTest "shiftL"           shiftL
     ++ genIntTest "shiftR"           shiftR
     ++ genIntTest "rotateL"          rotateL
     ++ genIntTest "rotateR"          rotateR
     ++ genBlasts

genBinTest :: String -> (forall a. Bits a => a -> a -> a) -> [Test]
genBinTest nm op = map mkTest $
        zipWith pair [(show x, show y, x `op` y) | x <- w8s,  y <- w8s ] [x `op` y | x <- sw8s,  y <- sw8s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- w16s, y <- w16s] [x `op` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- w32s, y <- w32s] [x `op` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- w64s, y <- w64s] [x `op` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i8s,  y <- i8s ] [x `op` y | x <- si8s,  y <- si8s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i16s, y <- i16s] [x `op` y | x <- si16s, y <- si16s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i32s, y <- i32s] [x `op` y | x <- si32s, y <- si32s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i64s, y <- i64s] [x `op` y | x <- si64s, y <- si64s]
  where pair (x, y, a) b   = (x, y, show ((fromIntegral a) `asTypeOf` b) == show b)
        mkTest (x, y, s) = "arithmetic-" ++ nm ++ "." ++ x ++ "_" ++ y  ~: s `showsAs` "True"

genUnTest :: String -> (forall a. Bits a => a -> a) -> [Test]
genUnTest nm op = map mkTest $
        zipWith pair [(show x, op x) | x <- w8s ] [op x | x <- sw8s ]
     ++ zipWith pair [(show x, op x) | x <- w16s] [op x | x <- sw16s]
     ++ zipWith pair [(show x, op x) | x <- w32s] [op x | x <- sw32s]
     ++ zipWith pair [(show x, op x) | x <- w64s] [op x | x <- sw64s]
     ++ zipWith pair [(show x, op x) | x <- i8s ] [op x | x <- si8s ]
     ++ zipWith pair [(show x, op x) | x <- i16s] [op x | x <- si16s]
     ++ zipWith pair [(show x, op x) | x <- i32s] [op x | x <- si32s]
     ++ zipWith pair [(show x, op x) | x <- i64s] [op x | x <- si64s]
  where pair (x, a) b   = (x, show ((fromIntegral a) `asTypeOf` b) == show b)
        mkTest (x, s) = "arithmetic-" ++ nm ++ "." ++ x ~: s `showsAs` "True"

genIntTest :: String -> (forall a. Bits a => a -> Int -> a) -> [Test]
genIntTest nm op = map mkTest $
        zipWith pair [("u8",  show x, show y, x `op` y) | x <- w8s,  y <- is] [x `op` y | x <- sw8s,  y <- is]
     ++ zipWith pair [("u16", show x, show y, x `op` y) | x <- w16s, y <- is] [x `op` y | x <- sw16s, y <- is]
     ++ zipWith pair [("u32", show x, show y, x `op` y) | x <- w32s, y <- is] [x `op` y | x <- sw32s, y <- is]
     ++ zipWith pair [("u64", show x, show y, x `op` y) | x <- w64s, y <- is] [x `op` y | x <- sw64s, y <- is]
     ++ zipWith pair [("s8",  show x, show y, x `op` y) | x <- i8s,  y <- is] [x `op` y | x <- si8s,  y <- is]
     ++ zipWith pair [("s16", show x, show y, x `op` y) | x <- i16s, y <- is] [x `op` y | x <- si16s, y <- is]
     ++ zipWith pair [("s32", show x, show y, x `op` y) | x <- i32s, y <- is] [x `op` y | x <- si32s, y <- is]
     ++ zipWith pair [("s64", show x, show y, x `op` y) | x <- i64s, y <- is] [x `op` y | x <- si64s, y <- is]
  where pair (t, x, y, a) b       = (t, x, y, show a, show b, show ((fromIntegral a) `asTypeOf` b) == show b)
        mkTest (t, x, y, a, b, s) = "arithmetic-" ++ nm ++ "." ++ t ++ "_" ++ x ++ "_" ++ y ++ "_" ++ a ++ "_" ++ b ~: s `showsAs` "True"
        is = [-10 .. 10]

genBlasts :: [Test]
genBlasts = map mkTest $
             [(show x, fromBitsLE (blastLE x) .== x) | x <- sw8s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw8s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si8s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si8s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- sw16s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw16s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si16s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si16s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- sw32s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw32s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si32s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si32s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- sw64s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw64s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si64s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si64s ]
  where mkTest (x, r) = "blast-" ++ show x ~: r `showsAs` "True"

-- Concrete test data
xsSigned, xsUnsigned :: (Num a, Enum a, Bounded a) => [a]
xsUnsigned = take 5 (iterate (1+) minBound) ++ take 5 (iterate (\x -> x-1) maxBound)
xsSigned   = xsUnsigned ++ [-5 .. 5]

w8s :: [Word8]
w8s = xsUnsigned

sw8s :: [SWord8]
sw8s = xsUnsigned

w16s :: [Word16]
w16s = xsUnsigned

sw16s :: [SWord16]
sw16s = xsUnsigned

w32s :: [Word32]
w32s = xsUnsigned

sw32s :: [SWord32]
sw32s = xsUnsigned

w64s :: [Word64]
w64s = xsUnsigned

sw64s :: [SWord64]
sw64s = xsUnsigned

i8s :: [Int8]
i8s = xsSigned

si8s :: [SInt8]
si8s = xsSigned

i16s :: [Int16]
i16s = xsSigned

si16s :: [SInt16]
si16s = xsSigned

i32s :: [Int32]
i32s = xsSigned

si32s :: [SInt32]
si32s = xsSigned

i64s :: [Int64]
i64s = xsSigned

si64s :: [SInt64]
si64s = xsSigned
