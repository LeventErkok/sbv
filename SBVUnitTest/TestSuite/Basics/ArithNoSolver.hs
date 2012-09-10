-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.ArithNoSolver
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for basic concrete arithmetic, i.e., testing all
-- the constant folding based arithmetic implementation in SBV
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types    #-}
{-# LANGUAGE TupleSections #-}

module TestSuite.Basics.ArithNoSolver(testSuite) where

import Data.SBV

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test $
        genReals
     ++ genQRems
     ++ genBinTest  "+"                (+)
     ++ genBinTest  "-"                (-)
     ++ genBinTest  "*"                (*)
     ++ genUnTest   "negate"           negate
     ++ genUnTest   "abs"              abs
     ++ genUnTest   "signum"           signum
     ++ genBinTest  ".&."              (.&.)
     ++ genBinTest  ".|."              (.|.)
     ++ genBoolTest "<"                (<)  (.<)
     ++ genBoolTest "<="               (<=) (.<=)
     ++ genBoolTest ">"                (>)  (.>)
     ++ genBoolTest ">="               (>=) (.>=)
     ++ genBoolTest "=="               (==) (.==)
     ++ genBoolTest "/="               (/=) (./=)
     ++ genBinTest  "xor"              xor
     ++ genUnTest   "complement"       complement
     ++ genIntTest  "shift"            shift
     ++ genIntTest  "rotate"           rotate
     ++ genIntTestS "setBit"           setBit
     ++ genIntTestS "clearBit"         clearBit
     ++ genIntTestS "complementBit"    complementBit
     ++ genIntTest  "shift"            shift
     ++ genIntTestS "shiftL"           shiftL
     ++ genIntTestS "shiftR"           shiftR
     ++ genIntTest  "rotate"           rotate
     ++ genIntTestS "rotateL"          rotateL
     ++ genIntTestS "rotateR"          rotateR
     ++ genBlasts
     ++ genCasts

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
     ++ zipWith pair [(show x, show y, x `op` y) | x <- iUBs, y <- iUBs] [x `op` y | x <- siUBs, y <- siUBs]
  where pair (x, y, a) b   = (x, y, show (fromIntegral a `asTypeOf` b) == show b)
        mkTest (x, y, s) = "arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y  ~: s `showsAs` "True"

genBoolTest :: String -> (forall a. Ord a => a -> a -> Bool) -> (forall a. OrdSymbolic a => a -> a -> SBool) -> [Test]
genBoolTest nm op opS = map mkTest $
        zipWith pair [(show x, show y, x `op` y) | x <- w8s,  y <- w8s ] [x `opS` y | x <- sw8s,  y <- sw8s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- w16s, y <- w16s] [x `opS` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- w32s, y <- w32s] [x `opS` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- w64s, y <- w64s] [x `opS` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i8s,  y <- i8s ] [x `opS` y | x <- si8s,  y <- si8s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i16s, y <- i16s] [x `opS` y | x <- si16s, y <- si16s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i32s, y <- i32s] [x `opS` y | x <- si32s, y <- si32s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- i64s, y <- i64s] [x `opS` y | x <- si64s, y <- si64s]
     ++ zipWith pair [(show x, show y, x `op` y) | x <- iUBs, y <- iUBs] [x `opS` y | x <- siUBs, y <- siUBs]
  where pair (x, y, a) b   = (x, y, Just a == unliteral b)
        mkTest (x, y, s) = "arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y  ~: s `showsAs` "True"

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
     ++ zipWith pair [(show x, op x) | x <- iUBs] [op x | x <- siUBs]
  where pair (x, a) b   = (x, show (fromIntegral a `asTypeOf` b) == show b)
        mkTest (x, s) = "arithCF-" ++ nm ++ "." ++ x ~: s `showsAs` "True"

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
     ++ zipWith pair [("iUB", show x, show y, x `op` y) | x <- iUBs, y <- is] [x `op` y | x <- siUBs, y <- is]
  where pair (t, x, y, a) b       = (t, x, y, show a, show b, show (fromIntegral a `asTypeOf` b) == show b)
        mkTest (t, x, y, a, b, s) = "arithCF-" ++ nm ++ "." ++ t ++ "_" ++ x ++ "_" ++ y ++ "_" ++ a ++ "_" ++ b ~: s `showsAs` "True"
        is = [-10 .. 10]

genIntTestS :: String -> (forall a. Bits a => a -> Int -> a) -> [Test]
genIntTestS nm op = map mkTest $
        zipWith pair [("u8",  show x, show y, x `op` y) | x <- w8s,  y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- sw8s,  y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("u16", show x, show y, x `op` y) | x <- w16s, y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- sw16s, y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("u32", show x, show y, x `op` y) | x <- w32s, y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- sw32s, y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("u64", show x, show y, x `op` y) | x <- w64s, y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- sw64s, y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("s8",  show x, show y, x `op` y) | x <- i8s,  y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- si8s,  y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("s16", show x, show y, x `op` y) | x <- i16s, y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- si16s, y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("s32", show x, show y, x `op` y) | x <- i32s, y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- si32s, y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("s64", show x, show y, x `op` y) | x <- i64s, y <- [0 .. (bitSize x - 1)]] [x `op` y | x <- si64s, y <- [0 .. (bitSize x - 1)]]
     ++ zipWith pair [("iUB", show x, show y, x `op` y) | x <- iUBs, y <- [0 .. 10]]              [x `op` y | x <- siUBs, y <- [0 .. 10             ]]
  where pair (t, x, y, a) b       = (t, x, y, show a, show b, show (fromIntegral a `asTypeOf` b) == show b)
        mkTest (t, x, y, a, b, s) = "arithCF-" ++ nm ++ "." ++ t ++ "_" ++ x ++ "_" ++ y ++ "_" ++ a ++ "_" ++ b ~: s `showsAs` "True"

genBlasts :: [Test]
genBlasts = map mkTest $
             [(show x, fromBitsLE (blastLE x) .== x) | x <- sw8s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw8s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si8s ]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si8s ]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- sw16s]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw16s]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si16s]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si16s]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- sw32s]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw32s]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si32s]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si32s]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- sw64s]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- sw64s]
          ++ [(show x, fromBitsLE (blastLE x) .== x) | x <- si64s]
          ++ [(show x, fromBitsBE (blastBE x) .== x) | x <- si64s]
  where mkTest (x, r) = "blast-" ++ show x ~: r `showsAs` "True"

genCasts :: [Test]
genCasts = map mkTest $
            [(show x, unsignCast (signCast x) .== x) | x <- sw8s ]
         ++ [(show x, unsignCast (signCast x) .== x) | x <- sw16s]
         ++ [(show x, unsignCast (signCast x) .== x) | x <- sw32s]
         ++ [(show x, unsignCast (signCast x) .== x) | x <- sw64s]
         ++ [(show x, signCast (unsignCast x) .== x) | x <- si8s ]
         ++ [(show x, signCast (unsignCast x) .== x) | x <- si16s]
         ++ [(show x, signCast (unsignCast x) .== x) | x <- si8s ]
         ++ [(show x, signCast (unsignCast x) .== x) | x <- si16s]
         ++ [(show x, signCast (unsignCast x) .== x) | x <- si32s]
         ++ [(show x, signCast (unsignCast x) .== x) | x <- si64s]
         ++ [(show x, signCast x .== fromBitsLE (blastLE x))   | x <- sw8s ]
         ++ [(show x, signCast x .== fromBitsLE (blastLE x))   | x <- sw16s]
         ++ [(show x, signCast x .== fromBitsLE (blastLE x))   | x <- sw32s]
         ++ [(show x, signCast x .== fromBitsLE (blastLE x))   | x <- sw64s]
         ++ [(show x, unsignCast x .== fromBitsLE (blastLE x)) | x <- si8s ]
         ++ [(show x, unsignCast x .== fromBitsLE (blastLE x)) | x <- si16s]
         ++ [(show x, unsignCast x .== fromBitsLE (blastLE x)) | x <- si32s]
         ++ [(show x, unsignCast x .== fromBitsLE (blastLE x)) | x <- si64s]
  where mkTest (x, r) = "cast-" ++ show x ~: r `showsAs` "True"

genQRems :: [Test]
genQRems = map mkTest $
        zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- w8s,  y <- w8s ]                 [x `sDivMod`  y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- w16s, y <- w16s]                 [x `sDivMod`  y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- w32s, y <- w32s]                 [x `sDivMod`  y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- w64s, y <- w64s]                 [x `sDivMod`  y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- i8s,  y <- i8s , noOverflow x y] [x `sDivMod`  y | x <- si8s,  y <- si8s , noOverflow x y]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- i16s, y <- i16s, noOverflow x y] [x `sDivMod`  y | x <- si16s, y <- si16s, noOverflow x y]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- i32s, y <- i32s, noOverflow x y] [x `sDivMod`  y | x <- si32s, y <- si32s, noOverflow x y]
     ++ (if divModInt64Bug    -- see below
            then []
            else zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- i64s, y <- i64s, noOverflow x y] [x `sDivMod`  y | x <- si64s, y <- si64s, noOverflow x y]
        )
     ++ zipWith pair [("divMod",  show x, show y, x `divMod'`  y) | x <- iUBs, y <- iUBs]                 [x `sDivMod`  y | x <- siUBs, y <- siUBs]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- w8s,  y <- w8s ]                 [x `sQuotRem` y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- w16s, y <- w16s]                 [x `sQuotRem` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- w32s, y <- w32s]                 [x `sQuotRem` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- w64s, y <- w64s]                 [x `sQuotRem` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- i8s,  y <- i8s , noOverflow x y] [x `sQuotRem` y | x <- si8s,  y <- si8s , noOverflow x y]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- i16s, y <- i16s, noOverflow x y] [x `sQuotRem` y | x <- si16s, y <- si16s, noOverflow x y]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- i32s, y <- i32s, noOverflow x y] [x `sQuotRem` y | x <- si32s, y <- si32s, noOverflow x y]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- i64s, y <- i64s, noOverflow x y] [x `sQuotRem` y | x <- si64s, y <- si64s, noOverflow x y]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem'` y) | x <- iUBs, y <- iUBs]                 [x `sQuotRem` y | x <- siUBs, y <- siUBs]
  where divMod'  x y = if y == 0 then (0, x) else x `divMod`  y
        quotRem' x y = if y == 0 then (0, x) else x `quotRem` y
        pair (nm, x, y, (r1, r2)) (e1, e2)   = (nm, x, y, show (fromIntegral r1 `asTypeOf` e1, fromIntegral r2 `asTypeOf` e2) == show (e1, e2))
        mkTest (nm, x, y, s) = "arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y  ~: s `showsAs` "True"
        -- Haskell's divMod and quotRem overflows if x == minBound and y == -1 for bounded signed types; so avoid that case
        noOverflow x y = not (x == minBound && y == -1)

genReals :: [Test]
genReals = map mkTest $
        map ("+",)  (zipWith pair [(show x, show y, x +  y) | x <- rs, y <- rs        ] [x +   y | x <- srs,  y <- srs                       ])
     ++ map ("-",)  (zipWith pair [(show x, show y, x -  y) | x <- rs, y <- rs        ] [x -   y | x <- srs,  y <- srs                       ])
     ++ map ("*",)  (zipWith pair [(show x, show y, x *  y) | x <- rs, y <- rs        ] [x *   y | x <- srs,  y <- srs                       ])
     ++ map ("<",)  (zipWith pair [(show x, show y, x <  y) | x <- rs, y <- rs        ] [x .<  y | x <- srs,  y <- srs                       ])
     ++ map ("<=",) (zipWith pair [(show x, show y, x <= y) | x <- rs, y <- rs        ] [x .<= y | x <- srs,  y <- srs                       ])
     ++ map (">",)  (zipWith pair [(show x, show y, x >  y) | x <- rs, y <- rs        ] [x .>  y | x <- srs,  y <- srs                       ])
     ++ map (">=",) (zipWith pair [(show x, show y, x >= y) | x <- rs, y <- rs        ] [x .>= y | x <- srs,  y <- srs                       ])
     ++ map ("==",) (zipWith pair [(show x, show y, x == y) | x <- rs, y <- rs        ] [x .== y | x <- srs,  y <- srs                       ])
     ++ map ("/=",) (zipWith pair [(show x, show y, x /= y) | x <- rs, y <- rs        ] [x ./= y | x <- srs,  y <- srs                       ])
     ++ map ("/",)  (zipWith pair [(show x, show y, x /  y) | x <- rs, y <- rs, y /= 0] [x / y   | x <- srs,  y <- srs, unliteral y /= Just 0])
  where pair (x, y, a) b   = (x, y, Just a == unliteral b)
        mkTest (nm, (x, y, s)) = "arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y  ~: s `showsAs` "True"

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

iUBs :: [Integer]
iUBs = [-1000000 .. -999995] ++ [-5 .. 5] ++ [999995 ..  1000000]

siUBs :: [SInteger]
siUBs = map literal iUBs

rs :: [AlgReal]
rs = [fromRational (i % d) | i <- is, d <- ds]
 where is = [-1000000 .. -999998] ++ [-2 .. 2] ++ [999998 ..  1000001]
       ds = [2 .. 5] ++ [98 .. 102] ++ [999998 .. 1000000]

srs :: [SReal]
srs = map literal rs


-- On 32 bit installations of GHC, divMod is buggy for Int64
-- Thus causing our tests to fail. See ticket: http://hackage.haskell.org/trac/ghc/ticket/7233
-- Luckily, it's easy to detect it and sidestep it until GHC is appropriately patched
divModInt64Bug :: Bool
divModInt64Bug = (1 `div` (minBound::Int64)) /= -1   -- Bug causes this expression to evaluate to 1
