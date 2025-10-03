-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ArithNoSolver
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for basic concrete arithmetic, i.e., testing all
-- the constant folding based arithmetic implementation in SBV
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types       #-}
{-# LANGUAGE TupleSections    #-}

#if MIN_VERSION_base(4,19,0)
{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns -Wno-x-partial #-}
#else
{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}
#endif

module TestSuite.Basics.ArithNoSolver(tests) where

import Data.SBV.Internals
import Utils.SBVTestFramework

import Data.Maybe (fromJust, fromMaybe)

import qualified Data.Char     as C

import qualified Data.SBV.Char () -- instances only

-- Test suite
tests :: TestTree
tests = testGroup "Arith.NoSolver" $
           genReals
        ++ genFloats
        ++ genQRems
        ++ genBinTest            "+"             (+)
        ++ genBinTest            "-"             (-)
        ++ genBinTest            "*"             (*)
        ++ genUnTest             "negate"        negate
        ++ genUnTest             "abs"           abs
        ++ genUnTest             "signum"        signum
        ++ genBitTest            ".&."           (.&.)
        ++ genBitTest            ".|."           (.|.)
        ++ genBoolTest           "<"             (<)  (.<)
        ++ genBoolTest           "<="            (<=) (.<=)
        ++ genBoolTest           ">"             (>)  (.>)
        ++ genBoolTest           ">="            (>=) (.>=)
        ++ genBoolTest           "=="            (==) (.==)
        ++ genBoolTest           "/="            (/=) (./=)
        ++ genBitTest            "xor"           xor
        ++ genUnTestBit          "complement"    complement

genBinTest :: String -> (forall a. Num a => a -> a -> a) -> [TestTree]
genBinTest nm op = map mkTest $
        zipWith pair [(show x, show y, literal (x `op` y)) | x <- w8s,  y <- w8s ] [x `op` y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- w16s, y <- w16s] [x `op` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- w32s, y <- w32s] [x `op` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- w64s, y <- w64s] [x `op` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i8s,  y <- i8s ] [x `op` y | x <- si8s,  y <- si8s ]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i16s, y <- i16s] [x `op` y | x <- si16s, y <- si16s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i32s, y <- i32s] [x `op` y | x <- si32s, y <- si32s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i64s, y <- i64s] [x `op` y | x <- si64s, y <- si64s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- iUBs, y <- iUBs] [x `op` y | x <- siUBs, y <- siUBs]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- rs,   y <- rs]   [x `op` y | x <- srs,   y <- srs]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- ras,  y <- ras]  [x `op` y | x <- sras,  y <- sras]
  where pair (x, y, a) b = (x, y, a == b)
        mkTest (x, y, s) = testCase ("arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y) (s `showsAs` "True")

genBitTest :: String -> (forall a. (Num a, Bits a) => a -> a -> a) -> [TestTree]
genBitTest nm op = map mkTest $
        zipWith pair [(show x, show y, literal (x `op` y)) | x <- w8s,  y <- w8s ] [x `op` y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- w16s, y <- w16s] [x `op` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- w32s, y <- w32s] [x `op` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- w64s, y <- w64s] [x `op` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i8s,  y <- i8s ] [x `op` y | x <- si8s,  y <- si8s ]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i16s, y <- i16s] [x `op` y | x <- si16s, y <- si16s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i32s, y <- i32s] [x `op` y | x <- si32s, y <- si32s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- i64s, y <- i64s] [x `op` y | x <- si64s, y <- si64s]
     ++ zipWith pair [(show x, show y, literal (x `op` y)) | x <- iUBs, y <- iUBs] [x `op` y | x <- siUBs, y <- siUBs]
  where pair (x, y, a) b = (x, y, a == b)
        mkTest (x, y, s) = testCase ("arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y) (s `showsAs` "True")

genBoolTest :: String -> (forall a. Ord a => a -> a -> Bool) -> (forall a. OrdSymbolic a => a -> a -> SBool) -> [TestTree]
genBoolTest nm op opS = map mkTest $
        zipWith pair [(show x, show y, x     `op` y)     | x <- w8s,  y <- w8s ] [x `opS` y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- w16s, y <- w16s] [x `opS` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- w32s, y <- w32s] [x `opS` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- w64s, y <- w64s] [x `opS` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- i8s,  y <- i8s ] [x `opS` y | x <- si8s,  y <- si8s ]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- i16s, y <- i16s] [x `opS` y | x <- si16s, y <- si16s]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- i32s, y <- i32s] [x `opS` y | x <- si32s, y <- si32s]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- i64s, y <- i64s] [x `opS` y | x <- si64s, y <- si64s]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- iUBs, y <- iUBs] [x `opS` y | x <- siUBs, y <- siUBs]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- iCs,  y <- iCs ] [x `opS` y | x <- siCs,  y <- siCs ]
     ++ zipWith pair [(show x, show y, x     `op` y)     | x <- ss,   y <- ss  ] [x `opS` y | x <- sss,   y <- sss  ]
     ++ zipWith pair [(show x, show y, toL x `op` toL y) | x <- ssl,  y <- ssl ] [x `opS` y | x <- ssl,   y <- ssl  ]
     ++ zipWith pair [(show x, show y, toL x `op` toL y) | x <- ssm,  y <- ssm ] [x `opS` y | x <- ssm,   y <- ssm  ]
     ++ zipWith pair [(show x, show y, toL x `op` toL y) | x <- sse,  y <- sse ] [x `opS` y | x <- sse,   y <- sse  ]
     ++ zipWith pair [(show x, show y, toL x `op` toL y) | x <- sst,  y <- sst ] [x `opS` y | x <- sst,   y <- sst  ]
     ++ zipWith pair [(show x, show y, toL x `op` toL y) | x <- sras, y <- sras] [x `opS` y | x <- sras,  y <- sras ]
  where pair (x, y, a) b = (x, y, Just a == unliteral b)
        mkTest (x, y, s) = testCase ("arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y) (s `showsAs` "True")
        toL x = fromMaybe (error "genBoolTest: Cannot extract a literal!") (unliteral x)

genUnTest :: String -> (forall a. Num a => a -> a) -> [TestTree]
genUnTest nm op = map mkTest $
        zipWith pair [(show x, literal (op x)) | x <- w8s ] [op x | x <- sw8s ]
     ++ zipWith pair [(show x, literal (op x)) | x <- w16s] [op x | x <- sw16s]
     ++ zipWith pair [(show x, literal (op x)) | x <- w32s] [op x | x <- sw32s]
     ++ zipWith pair [(show x, literal (op x)) | x <- w64s] [op x | x <- sw64s]
     ++ zipWith pair [(show x, literal (op x)) | x <- i8s ] [op x | x <- si8s ]
     ++ zipWith pair [(show x, literal (op x)) | x <- i16s] [op x | x <- si16s]
     ++ zipWith pair [(show x, literal (op x)) | x <- i32s] [op x | x <- si32s]
     ++ zipWith pair [(show x, literal (op x)) | x <- i64s] [op x | x <- si64s]
     ++ zipWith pair [(show x, literal (op x)) | x <- iUBs] [op x | x <- siUBs]
     ++ zipWith pair [(show x, literal (op x)) | x <- ras]  [op x | x <- sras]
  where pair (x, a) b = (x, a == b)
        mkTest (x, s) = testCase ("arithCF-" ++ nm ++ "." ++ x) (s `showsAs` "True")

genUnTestBit :: String -> (forall a. (Num a, Bits a) => a -> a) -> [TestTree]
genUnTestBit nm op = map mkTest $
        zipWith pair [(show x, op x) | x <- w8s ] [op x | x <- sw8s ]
     ++ zipWith pair [(show x, op x) | x <- w16s] [op x | x <- sw16s]
     ++ zipWith pair [(show x, op x) | x <- w32s] [op x | x <- sw32s]
     ++ zipWith pair [(show x, op x) | x <- w64s] [op x | x <- sw64s]
     ++ zipWith pair [(show x, op x) | x <- i8s ] [op x | x <- si8s ]
     ++ zipWith pair [(show x, op x) | x <- i16s] [op x | x <- si16s]
     ++ zipWith pair [(show x, op x) | x <- i32s] [op x | x <- si32s]
     ++ zipWith pair [(show x, op x) | x <- i64s] [op x | x <- si64s]
     ++ zipWith pair [(show x, op x) | x <- iUBs] [op x | x <- siUBs]
  where pair (x, a) b = (x, show (fromIntegral a `asTypeOf` b) == show b)
        mkTest (x, s) = testCase ("arithCF-" ++ nm ++ "." ++ x) (s `showsAs` "True")

genQRems :: [TestTree]
genQRems = map mkTest $
        zipWith pair [("divMod",  show x, show y, x `divMod0`  y) | x <- w8s,  y <- w8s ] [x `sDivMod`  y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod0`  y) | x <- w16s, y <- w16s] [x `sDivMod`  y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod0`  y) | x <- w32s, y <- w32s] [x `sDivMod`  y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod0`  y) | x <- w64s, y <- w64s] [x `sDivMod`  y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod1`  y) | x <- i8s,  y <- i8s ] [x `sDivMod`  y | x <- si8s,  y <- si8s ]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod1`  y) | x <- i16s, y <- i16s] [x `sDivMod`  y | x <- si16s, y <- si16s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod1`  y) | x <- i32s, y <- i32s] [x `sDivMod`  y | x <- si32s, y <- si32s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod1`  y) | x <- i64s, y <- i64s] [x `sDivMod`  y | x <- si64s, y <- si64s]
     ++ zipWith pair [("divMod",  show x, show y, x `divMod0`  y) | x <- iUBs, y <- iUBs] [x `sDivMod`  y | x <- siUBs, y <- siUBs]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem0` y) | x <- w8s,  y <- w8s ] [x `sQuotRem` y | x <- sw8s,  y <- sw8s ]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem0` y) | x <- w16s, y <- w16s] [x `sQuotRem` y | x <- sw16s, y <- sw16s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem0` y) | x <- w32s, y <- w32s] [x `sQuotRem` y | x <- sw32s, y <- sw32s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem0` y) | x <- w64s, y <- w64s] [x `sQuotRem` y | x <- sw64s, y <- sw64s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem1` y) | x <- i8s,  y <- i8s ] [x `sQuotRem` y | x <- si8s,  y <- si8s ]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem1` y) | x <- i16s, y <- i16s] [x `sQuotRem` y | x <- si16s, y <- si16s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem1` y) | x <- i32s, y <- i32s] [x `sQuotRem` y | x <- si32s, y <- si32s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem1` y) | x <- i64s, y <- i64s] [x `sQuotRem` y | x <- si64s, y <- si64s]
     ++ zipWith pair [("quotRem", show x, show y, x `quotRem0` y) | x <- iUBs, y <- iUBs] [x `sQuotRem` y | x <- siUBs, y <- siUBs]
  where pair (nm, x, y, (r1, r2)) (e1, e2)   = (nm, x, y, show (fromIntegral r1 `asTypeOf` e1, fromIntegral r2 `asTypeOf` e2) == show (e1, e2))
        mkTest (nm, x, y, s) = testCase ("arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y) (s `showsAs` "True")
        -- Haskell's divMod and quotRem differs from SBV's in two ways:
        --     - when y is 0, Haskell throws an exception, SBV sets the result to 0; like in division
        --     - Haskell overflows if x == minBound and y == -1 for bounded signed types; but SBV returns minBound, 0; which is more meaningful
        overflow x y = x == minBound && y == -1
        divMod0  x y = if y == 0       then (0, x) else x `divMod`   y
        divMod1  x y = if overflow x y then (x, 0) else x `divMod0`  y
        quotRem0 x y = if y == 0       then (0, x) else x `quotRem`  y
        quotRem1 x y = if overflow x y then (x, 0) else x `quotRem0` y

genReals :: [TestTree]
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
        mkTest (nm, (x, y, s)) = testCase ("arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y) (s `showsAs` "True")

genFloats :: [TestTree]
genFloats = bTests ++ uTests ++ fpTests1 ++ fpTests2 ++ converts
  where bTests = map mkTest2 $  floatRun2  "+"  (+)  (+)   comb
                             ++ doubleRun2 "+"  (+)  (+)   comb

                             ++ floatRun2  "-"  (-)  (-)   comb
                             ++ doubleRun2 "-"  (-)  (-)   comb

                             ++ floatRun2  "*"  (*)  (*)   comb
                             ++ doubleRun2 "*"  (*)  (*)   comb

                             ++ floatRun2  "/"  (/)  (/)   comb
                             ++ doubleRun2 "/"  (/)  (/)   comb

                             ++ floatRun2  "<"  (<)  (.<)  combB
                             ++ doubleRun2 "<"  (<)  (.<)  combB

                             ++ floatRun2  "<=" (<=) (.<=) combB
                             ++ doubleRun2 "<=" (<=) (.<=) combB

                             ++ floatRun2  ">"  (>)  (.>)  combB
                             ++ doubleRun2 ">"  (>)  (.>)  combB

                             ++ floatRun2  ">=" (>=) (.>=) combB
                             ++ doubleRun2 ">=" (>=) (.>=) combB

                             ++ floatRun2  "==" (==) (.==) combB
                             ++ doubleRun2 "==" (==) (.==) combB

                             ++ floatRun2  "/=" (/=) (./=) combN
                             ++ doubleRun2 "/=" (/=) (./=) combN

        fpTests1 = map mkTest1 $  floatRun1   "abs"               abs                abs               comb1
                               ++ floatRun1   "fpAbs"             abs                fpAbs             comb1
                               ++ doubleRun1  "abs"               abs                abs               comb1
                               ++ doubleRun1  "fpAbs"             abs                fpAbs             comb1

                               ++ floatRun1   "negate"            negate             negate            comb1
                               ++ floatRun1   "fpNeg"             negate             fpNeg             comb1
                               ++ doubleRun1  "negate"            negate             negate            comb1
                               ++ doubleRun1  "fpNeg"             negate             fpNeg             comb1

                               ++ floatRun1M  "fpSqrt"            sqrt               fpSqrt            comb1
                               ++ doubleRun1M "fpSqrt"            sqrt               fpSqrt            comb1

                               ++ floatRun1M  "fpRoundToIntegral" fpRoundToIntegralH fpRoundToIntegral comb1
                               ++ doubleRun1M "fpRoundToIntegral" fpRoundToIntegralH fpRoundToIntegral comb1

                               ++ floatRun1   "signum"            signum             signum            comb1
                               ++ doubleRun1  "signum"            signum             signum            comb1

        -- TODO. Can't possibly test fma, unless we FFI out to C. Leave it out for the time being
        fpTests2 = map mkTest2 $  floatRun2M  "fpAdd"           (+)              fpAdd           comb
                               ++ doubleRun2M "fpAdd"           (+)              fpAdd           comb

                               ++ floatRun2M  "fpSub"           (-)              fpSub           comb
                               ++ doubleRun2M "fpSub"           (-)              fpSub           comb

                               ++ floatRun2M  "fpMul"           (*)              fpMul           comb
                               ++ doubleRun2M "fpMul"           (*)              fpMul           comb

                               ++ floatRun2M  "fpDiv"           (/)              fpDiv           comb
                               ++ doubleRun2M "fpDiv"           (/)              fpDiv           comb

                               ++ floatRunMM  "fpMin"           fpMinH           fpMin           comb
                               ++ doubleRunMM "fpMin"           fpMinH           fpMin           comb

                               ++ floatRunMM  "fpMax"           fpMaxH           fpMax           comb
                               ++ doubleRunMM "fpMax"           fpMaxH           fpMax           comb

                               ++ floatRun2   "fpRem"           fpRemH           fpRem           comb
                               ++ doubleRun2  "fpRem"           fpRemH           fpRem           comb

                               ++ floatRun2   "fpIsEqualObject" fpIsEqualObjectH fpIsEqualObject combE
                               ++ doubleRun2  "fpIsEqualObject" fpIsEqualObjectH fpIsEqualObject combE

        converts =   [cvtTest ("toFP_Int8_ToFloat",     show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- i8s ]
                 ++  [cvtTest ("toFP_Int16_ToFloat",    show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- i16s]
                 ++  [cvtTest ("toFP_Int32_ToFloat",    show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- i32s]
                 ++  [cvtTest ("toFP_Int64_ToFloat",    show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- i64s]
                 ++  [cvtTest ("toFP_Word8_ToFloat",    show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- w8s ]
                 ++  [cvtTest ("toFP_Word16_ToFloat",   show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- w16s]
                 ++  [cvtTest ("toFP_Word32_ToFloat",   show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- w32s]
                 ++  [cvtTest ("toFP_Word64_ToFloat",   show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- w64s]
                 ++  [cvtTest ("toFP_Float_ToFloat",    show x, toSFloat  sRNE (literal x),                  literal x ) | x <- fs  ]
                 ++  [cvtTest ("toFP_Double_ToFloat",   show x, toSFloat  sRNE (literal x),           literal (fp2fp x)) | x <- ds  ]
                 ++  [cvtTest ("toFP_Integer_ToFloat",  show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- iUBs]
                 ++  [cvtTest ("toFP_Real_ToFloat",     show x, toSFloat  sRNE (literal x), fromRational (toRational x)) | x <- rs  ]

                 ++  [cvtTest ("toFP_Int8_ToDouble",    show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- i8s ]
                 ++  [cvtTest ("toFP_Int16_ToDouble",   show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- i16s]
                 ++  [cvtTest ("toFP_Int32_ToDouble",   show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- i32s]
                 ++  [cvtTest ("toFP_Int64_ToDouble",   show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- i64s]
                 ++  [cvtTest ("toFP_Word8_ToDouble",   show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- w8s ]
                 ++  [cvtTest ("toFP_Word16_ToDouble",  show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- w16s]
                 ++  [cvtTest ("toFP_Word32_ToDouble",  show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- w32s]
                 ++  [cvtTest ("toFP_Word64_ToDouble",  show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- w64s]
                 ++  [cvtTest ("toFP_Float_ToDouble",   show x, toSDouble sRNE (literal x),           literal (fp2fp x)) | x <- fs  ]
                 ++  [cvtTest ("toFP_Double_ToDouble",  show x, toSDouble sRNE (literal x),                   literal x) | x <- ds  ]
                 ++  [cvtTest ("toFP_Integer_ToDouble", show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- iUBs]
                 ++  [cvtTest ("toFP_Real_ToDouble",    show x, toSDouble sRNE (literal x), fromRational (toRational x)) | x <- rs  ]

                 -- NB. We don't constant fold float/double conversions, so we skip these
                 --
                 ++  [cvtTest  ("reinterp_Word32_Float",  show x, sWord32AsSFloat  (literal x), literal (wordToFloat  x)) | x <- w32s]
                 ++  [cvtTest  ("reinterp_Word64_Double", show x, sWord64AsSDouble (literal x), literal (wordToDouble x)) | x <- w64s]

                 ++  [cvtTestI ("reinterp_Float_Word32",  show x, sFloatAsSWord32  (literal x), floatToWord x)  | x <- fs, not (isNaN x)] -- Not unique for NaN
                 ++  [cvtTestI ("reinterp_Double_Word64", show x, sDoubleAsSWord64 (literal x), doubleToWord x) | x <- ds, not (isNaN x)] -- Not unique for NaN

        floatRun1   nm f g cmb = [(nm, cmb (x,    f x,   extract (g                     (literal x))))             | x <- fs]
        doubleRun1  nm f g cmb = [(nm, cmb (x,    f x,   extract (g                     (literal x))))             | x <- ds]
        floatRun1M  nm f g cmb = [(nm, cmb (x,    f x,   extract (g sRNE (literal x))))                            | x <- fs]
        doubleRun1M nm f g cmb = [(nm, cmb (x,    f x,   extract (g sRNE (literal x))))                            | x <- ds]
        floatRun2   nm f g cmb = [(nm, cmb (x, y, f x y, extract (g                     (literal x) (literal y)))) | x <- fs, y <- fs]
        doubleRun2  nm f g cmb = [(nm, cmb (x, y, f x y, extract (g                     (literal x) (literal y)))) | x <- ds, y <- ds]
        floatRun2M  nm f g cmb = [(nm, cmb (x, y, f x y, extract (g sRNE (literal x)    (literal y))))             | x <- fs, y <- fs]
        doubleRun2M nm f g cmb = [(nm, cmb (x, y, f x y, extract (g sRNE (literal x)    (literal y))))             | x <- ds, y <- ds]
        floatRunMM  nm f g cmb = [(nm, cmb (x, y, f x y, extract (g                     (literal x) (literal y)))) | x <- fs, y <- fs, not (alt0 x y || alt0 y x)]
        doubleRunMM nm f g cmb = [(nm, cmb (x, y, f x y, extract (g                     (literal x) (literal y)))) | x <- ds, y <- ds, not (alt0 x y || alt0 y x)]
        -- fpMin/fpMax: skip +0/-0 case as this is underspecified
        alt0 x y = isNegativeZero x && y == 0 && not (isNegativeZero y)
        uTests = map mkTest1 $  concatMap (checkPred fs sfs) predicates
                             ++ concatMap (checkPred ds sds) predicates
        extract :: SymVal a => SBV a -> a
        extract = fromJust . unliteral

        comb  (x, y, a, b) = (show x, show y, same a b)
        combB (x, y, a, b) = (show x, show y, checkNaN f x y a b) where f v w = not (v || w)  -- All comparisons except /=: Both should be False if we have a NaN argument
        combN (x, y, a, b) = (show x, show y, checkNaN f x y a b) where f v w =      v && w   -- /=: Both should be True
        combE (x, y, a, b) = (show x, show y, a == b)
        comb1 (x, a, b)    = (show x, same a b)
        same a b = (isNaN a && isNaN b) || (a == b)
        checkNaN f x y a b
          | isNaN x || isNaN y = f a b
          | True               = a == b

        cvtTest  (nm, x, a, b)  = testCase ("fpConverts.arithmetic-CF-" ++ nm ++ "." ++ x) (same (extract a) (extract b) `showsAs` "True")
        cvtTestI (nm, x, a, b)  = testCase ("fpConverts.arithmetic-CF-" ++ nm ++ "." ++ x) ((a .== literal b) `showsAs` "True")

        mkTest1 (nm, (x, s))    = testCase ("arithCF-" ++ nm ++ "." ++ x) (s `showsAs` "True")
        mkTest2 (nm, (x, y, s)) = testCase ("arithCF-" ++ nm ++ "." ++ x ++ "_" ++ y) (s `showsAs` "True")

        checkPred :: Show a => [a] -> [SBV a] -> (String, SBV a -> SBool, a -> Bool) -> [(String, (String, Bool))]
        checkPred xs sxs (n, ps, p) = zipWith (chk n) (map (\x -> (x, p x)) xs) (map ps sxs)
          where chk nm (x, v) sv = (nm, (show x, Just v == unliteral sv))

        predicates :: IEEEFloating a => [(String, SBV a -> SBool, a -> Bool)]
        predicates = [ ("fpIsNormal",       fpIsNormal,        fpIsNormalizedH)
                     , ("fpIsSubnormal",    fpIsSubnormal,     isDenormalized)
                     , ("fpIsZero",         fpIsZero,          (== 0))
                     , ("fpIsInfinite",     fpIsInfinite,      isInfinite)
                     , ("fpIsNaN",          fpIsNaN,           isNaN)
                     , ("fpIsNegative",     fpIsNegative,      \x -> x < 0  ||      isNegativeZero x)
                     , ("fpIsPositive",     fpIsPositive,      \x -> x >= 0 && not (isNegativeZero x))
                     , ("fpIsNegativeZero", fpIsNegativeZero,  isNegativeZero)
                     , ("fpIsPositiveZero", fpIsPositiveZero,  \x -> x == 0 && not (isNegativeZero x))
                     , ("fpIsPoint",        fpIsPoint,         \x -> not (isNaN x || isInfinite x))
                     ]

-- Concrete test data
xsUnsigned :: (Num a, Bounded a) => [a]
xsUnsigned = take 5 (iterate (1+) minBound) ++ take 5 (iterate (\x -> x-1) maxBound)

xsSigned :: (Num a, Enum a, Bounded a) => [a]
xsSigned   = xsUnsigned ++ [-5 .. 5]

w8s :: [Word8]
w8s = xsUnsigned

sw8s :: [SWord8]
sw8s = map literal xsUnsigned

w16s :: [Word16]
w16s = xsUnsigned

sw16s :: [SWord16]
sw16s = map literal xsUnsigned

w32s :: [Word32]
w32s = xsUnsigned

sw32s :: [SWord32]
sw32s = map literal xsUnsigned

w64s :: [Word64]
w64s = xsUnsigned

sw64s :: [SWord64]
sw64s = map literal xsUnsigned

i8s :: [Int8]
i8s = xsSigned

si8s :: [SInt8]
si8s = map literal xsSigned

i16s :: [Int16]
i16s = xsSigned

si16s :: [SInt16]
si16s = map literal xsSigned

i32s :: [Int32]
i32s = xsSigned

si32s :: [SInt32]
si32s = map literal xsSigned

i64s :: [Int64]
i64s = xsSigned

si64s :: [SInt64]
si64s = map literal xsSigned

iUBs :: [Integer]
iUBs = [-1000000 .. -999995] ++ [-5 .. 5] ++ [999995 ..  1000000]

siUBs :: [SInteger]
siUBs = map literal iUBs

ras :: [Rational]
ras = [i % d | i <- nums, d <- dens]
 where nums = [-1000000 .. -999998] ++ [-2 .. 2] ++ [999998 ..  1000001]
       dens = [2 .. 5] ++ [98 .. 102] ++ [999998 .. 1000000]

sras :: [SRational]
sras = map literal ras

rs :: [AlgReal]
rs = map fromRational ras

srs :: [SReal]
srs = map literal rs

fs :: [Float]
fs = xs ++ map (* (-1)) (filter (not . isNaN) xs) -- -nan is the same as nan
 where xs = [nan, infinity, 0, 0.5, 0.68302244, 0.5268265, 0.10283524, 5.8336496e-2, 1.0e-45]

sfs :: [SFloat]
sfs = map literal fs

ds :: [Double]
ds = xs ++ map (* (-1)) (filter (not . isNaN) xs) -- -nan is the same as nan
 where xs = [nan, infinity, 0, 0.5, 2.516632060108026e-2, 0.8601891300751106, 7.518897767550192e-2, 1.1656043286207285e-2, 5.0e-324]

sds :: [SDouble]
sds = map literal ds

-- For pair character ops, just take a subset
iCs :: [Char]
iCs = map C.chr $ [0..5] ++ [98..102] ++ [250..255]

siCs :: [SChar]
siCs = map literal iCs

-- Ditto for strings, just a few things
ss :: [String]
ss = ["", "palTRY", "teSTing", "SBV", "sTRIngs", "123", "surely", "thIS", "hI", "ly", "0"]

sss :: [SString]
sss = map literal ss

-- Lists are the worst in coverage!
sl :: [[Integer]]
sl = [[], [0], [-1, 1], [-10, 0, 10], [3, 4, 5, 4, 5, 3]]

-- Lists are the worst in coverage!
ssl :: [SList Integer]
ssl = map literal sl

-- Very rudimentary maybe, either, and, tuples
sm :: [Maybe Integer]
sm = [Nothing, Just (-5), Just 0, Just 5]

ssm :: [SMaybe Integer]
ssm = map literal sm

se :: [Either Integer Integer]
se = [Left 3, Right 5]

sse :: [SEither Integer Integer]
sse = map literal se

st :: [(Integer, Integer)]
st = [(1, 2), (-1, -5), (0, 9), (5, 5)]

sst :: [STuple Integer Integer]
sst = map literal st
{- HLint ignore module "Reduce duplication" -}
