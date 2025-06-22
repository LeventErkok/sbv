-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ArithNoSolver2
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Spill over from ArithNoSolver. To aid faster GHC compilation.
-- the constant folding based arithmetic implementation in SBV
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types       #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes      #-}

#if MIN_VERSION_base(4,19,0)
{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns -Wno-x-partial #-}
#else
{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}
#endif

module TestSuite.Basics.ArithNoSolver2(tests) where

import Data.SBV.Internals
import Utils.SBVTestFramework

import Data.Maybe (isJust)

import Data.List (genericIndex, isInfixOf, isPrefixOf, isSuffixOf, genericTake, genericDrop, genericLength)

import qualified Data.Char       as C
import qualified Data.SBV.Char   as SC
import qualified Data.SBV.List   as SL

-- Test suite
tests :: TestTree
tests = testGroup "Arith.NoSolver" $
           genIntTest      False "setBit"        setBit
        ++ genIntTest      False "clearBit"      clearBit
        ++ genIntTest      False "complementBit" complementBit
        ++ genIntTest      True  "shift"         shift
        ++ genIntTest      True  "shiftL"        shiftL
        ++ genIntTest      True  "shiftR"        shiftR
        ++ genIntTest      True  "rotate"        rotate
        ++ genIntTest      True  "rotateL"       rotateL
        ++ genIntTest      True  "rotateR"       rotateR
        ++ genShiftRotTest       "shiftL_gen"    sShiftLeft
        ++ genShiftRotTest       "shiftR_gen"    sShiftRight
        ++ genShiftRotTest       "rotateL_gen"   sRotateLeft
        ++ genShiftRotTest       "rotateR_gen"   sRotateRight
        ++ genShiftMixSize
        ++ genBlasts
        ++ genCounts
        ++ genIntCasts
        ++ genChars
        ++ genStrings
        ++ genLists
        ++ genEnums

genIntTest :: Bool -> String -> (forall a. (Num a, Bits a) => (a -> Int -> a)) -> [TestTree]
genIntTest overSized nm op = map mkTest $
        zipWith pair [("u8",  show x, show y, x `op` y) | x <- w8s,  y <- is (intSizeOf x)] [x `op` y | x <- sw8s,  y <- is (intSizeOf x)]
     ++ zipWith pair [("u16", show x, show y, x `op` y) | x <- w16s, y <- is (intSizeOf x)] [x `op` y | x <- sw16s, y <- is (intSizeOf x)]
     ++ zipWith pair [("u32", show x, show y, x `op` y) | x <- w32s, y <- is (intSizeOf x)] [x `op` y | x <- sw32s, y <- is (intSizeOf x)]
     ++ zipWith pair [("u64", show x, show y, x `op` y) | x <- w64s, y <- is (intSizeOf x)] [x `op` y | x <- sw64s, y <- is (intSizeOf x)]
     ++ zipWith pair [("s8",  show x, show y, x `op` y) | x <- i8s,  y <- is (intSizeOf x)] [x `op` y | x <- si8s,  y <- is (intSizeOf x)]
     ++ zipWith pair [("s16", show x, show y, x `op` y) | x <- i16s, y <- is (intSizeOf x)] [x `op` y | x <- si16s, y <- is (intSizeOf x)]
     ++ zipWith pair [("s32", show x, show y, x `op` y) | x <- i32s, y <- is (intSizeOf x)] [x `op` y | x <- si32s, y <- is (intSizeOf x)]
     ++ zipWith pair [("s64", show x, show y, x `op` y) | x <- i64s, y <- is (intSizeOf x)] [x `op` y | x <- si64s, y <- is (intSizeOf x)]
     ++ zipWith pair [("iUB", show x, show y, x `op` y) | x <- iUBs, y <- [0..10]]          [x `op` y | x <- siUBs, y <- [0..10]]
  where is sz = [0 .. sz - 1] ++ extras
          where extras
                 | overSized = map (sz +) ([0 .. 1] ++ [sz, sz+1])
                 | True      = []
        pair (t, x, y, a) b       = (t, x, y, show a, show b, show (fromIntegral a `asTypeOf` b) == show b)
        mkTest (t, x, y, a, b, s) = testCase ("arithCF-" ++ nm ++ "." ++ t ++ "_" ++ x ++ "_" ++ y ++ "_" ++ a ++ "_" ++ b) (s `showsAs` "True")

genShiftRotTest :: String -> (forall a. (SIntegral a, SDivisible (SBV a)) => (SBV a -> SBV a -> SBV a)) -> [TestTree]
genShiftRotTest nm op = map mkTest $
        zipWith pair [("u8",  show x, show y, literal x `op` y) | x <- w8s,  y <- is (intSizeOf x)] [x `op` y | x <- sw8s,  y <- is (intSizeOf x)]
     ++ zipWith pair [("u16", show x, show y, literal x `op` y) | x <- w16s, y <- is (intSizeOf x)] [x `op` y | x <- sw16s, y <- is (intSizeOf x)]
     ++ zipWith pair [("u32", show x, show y, literal x `op` y) | x <- w32s, y <- is (intSizeOf x)] [x `op` y | x <- sw32s, y <- is (intSizeOf x)]
     ++ zipWith pair [("u64", show x, show y, literal x `op` y) | x <- w64s, y <- is (intSizeOf x)] [x `op` y | x <- sw64s, y <- is (intSizeOf x)]
     ++ zipWith pair [("s8",  show x, show y, literal x `op` y) | x <- i8s,  y <- is (intSizeOf x)] [x `op` y | x <- si8s,  y <- is (intSizeOf x)]
     ++ zipWith pair [("s16", show x, show y, literal x `op` y) | x <- i16s, y <- is (intSizeOf x)] [x `op` y | x <- si16s, y <- is (intSizeOf x)]
     ++ zipWith pair [("s32", show x, show y, literal x `op` y) | x <- i32s, y <- is (intSizeOf x)] [x `op` y | x <- si32s, y <- is (intSizeOf x)]
     ++ zipWith pair [("s64", show x, show y, literal x `op` y) | x <- i64s, y <- is (intSizeOf x)] [x `op` y | x <- si64s, y <- is (intSizeOf x)]
     -- NB. No generic shift/rotate for SMTLib unbounded integers
  where is sz = let b :: Word32
                    b = fromIntegral sz
                in map (sFromIntegral . literal) $ [0 .. b - 1] ++ [b, b+1, 2*b, 2*b+1]
        pair (t, x, y, a) b       = (t, x, y, show a, show b, isJust (unliteral a) && isJust (unliteral b) && unliteral a == unliteral b)
        mkTest (t, x, y, a, b, s) = testCase ("arithCF-" ++ nm ++ "." ++ t ++ "_" ++ x ++ "_" ++ y ++ "_" ++ a ++ "_" ++ b) (s `showsAs` "True")

-- A few tests for mixed-size shifts
genShiftMixSize :: [TestTree]
genShiftMixSize = map mkTest $
           [pair (show x, show y, "shl_w8_w16", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- w8s,  y <- yw16s]
        ++ [pair (show x, show y, "shr_w8_w16", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- w8s,  y <- yw16s]
        ++ [pair (show x, show y, "shl_w16_w8", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- w16s, y <- w8s]
        ++ [pair (show x, show y, "shr_w16_w8", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- w16s, y <- w8s]
        ++ [pair (show x, show y, "shl_i8_i16", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- i8s,  y <- yi16s]
        ++ [pair (show x, show y, "shr_i8_i16", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- i8s,  y <- yi16s]
        ++ [pair (show x, show y, "shl_i16_i8", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- i16s, y <- i8s, y >= 0]
        ++ [pair (show x, show y, "shr_i16_i8", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- i16s, y <- i8s, y >= 0]
        ++ [pair (show x, show y, "shl_w8_i16", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- w8s,  y <- yi16s]
        ++ [pair (show x, show y, "shr_w8_i16", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- w8s,  y <- yi16s]
        ++ [pair (show x, show y, "shl_w16_i8", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- w16s, y <- i8s, y >= 0]
        ++ [pair (show x, show y, "shr_w16_i8", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- w16s, y <- i8s, y >= 0]
        ++ [pair (show x, show y, "shl_i8_w16", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- i8s,  y <- yw16s]
        ++ [pair (show x, show y, "shr_i8_w16", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- i8s,  y <- yw16s]
        ++ [pair (show x, show y, "shl_i16_w8", literal x `sShiftLeft`  literal y,  x `shiftL` fromIntegral y) | x <- i16s, y <- w8s]
        ++ [pair (show x, show y, "shr_i16_w8", literal x `sShiftRight` literal y,  x `shiftR` fromIntegral y) | x <- i16s, y <- w8s]
   where pair :: (Eq a, SymVal a, Show a) => (String, String, String, SBV a, a) -> (String, Bool)
         pair (x, y, l, sr, lr) = (l ++ "." ++ x ++ "_" ++ y ++ "_" ++  show (unliteral sr) ++ "_" ++ show lr, isJust (unliteral sr) && unliteral sr == Just lr)
         mkTest (l, s) = testCase ("arithCF-genShiftMixSize" ++ l) (s `showsAs` "True")

         yi16s :: [Int16]
         yi16s = [0, 255, 256, 257, maxBound]

         yw16s :: [Word16]
         yw16s = [0, 255, 256, 257, maxBound]


genBlasts :: [TestTree]
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
  where mkTest (x, r) = testCase ("blast-" ++ x) (r `showsAs` "True")

genCounts :: [TestTree]
genCounts = map mkTest $
             [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SWord8 )) | x <- sw8s ]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SWord8 )) | x <- sw8s ]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SInt8  )) | x <- si8s ]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SInt8  )) | x <- si8s ]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SWord16)) | x <- sw16s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SWord16)) | x <- sw16s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SInt16 )) | x <- si16s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SInt16 )) | x <- si16s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SWord32)) | x <- sw32s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SWord32)) | x <- sw32s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SInt32 )) | x <- si32s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SInt32 )) | x <- si32s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SWord64)) | x <- sw64s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SWord64)) | x <- sw64s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsBE (blastLE x) :: SInt64 )) | x <- si64s]
          ++ [(show x, sCountTrailingZeros x .== sCountLeadingZeros (fromBitsLE (blastBE x) :: SInt64 )) | x <- si64s]
  where mkTest (x, r) = testCase ("count-" ++ x) (r `showsAs` "True")

genIntCasts :: [TestTree]
genIntCasts = map mkTest $  cast w8s ++ cast w16s ++ cast w32s ++ cast w64s
                         ++ cast i8s ++ cast i16s ++ cast i32s ++ cast i64s
                         ++ cast iUBs
   where mkTest (x, r) = testCase ("intCast-" ++ x) (r `showsAs` "True")
         lhs x = sFromIntegral (literal x)
         rhs x = literal (fromIntegral x)
         cast :: forall a. (Show a, Integral a, SymVal a) => [a] -> [(String, SBool)]
         cast xs = toWords xs ++ toInts xs
         toWords xs =  [(show x, lhs x .== (rhs x :: SWord8 ))  | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SWord16))  | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SWord32))  | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SWord64))  | x <- xs]
         toInts  xs =  [(show x, lhs x .== (rhs x :: SInt8 ))   | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SInt16))   | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SInt32))   | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SInt64))   | x <- xs]
                    ++ [(show x, lhs x .== (rhs x :: SInteger)) | x <- xs]

genChars :: [TestTree]
genChars = map mkTest $  [("ord",           show c, check SC.ord             cord            c) | c <- cs]
                      ++ [("toLower",       show c, check SC.toLowerL1       C.toLower       c) | c <- cs]
                      ++ [("toUpper",       show c, check SC.toUpperL1       C.toUpper       c) | c <- cs]
                      ++ [("digitToInt",    show c, check SC.digitToInt      dig2Int         c) | c <- cs, digitToIntRange c]
                      ++ [("intToDigit",    show c, check SC.intToDigit      int2Dig         c) | c <- [0 .. 15]]
                      ++ [("isControl",     show c, check SC.isControlL1     C.isControl     c) | c <- cs]
                      ++ [("isSpace",       show c, check SC.isSpaceL1       C.isSpace       c) | c <- cs]
                      ++ [("isLower",       show c, check SC.isLowerL1       C.isLower       c) | c <- cs]
                      ++ [("isUpper",       show c, check SC.isUpperL1       C.isUpper       c) | c <- cs]
                      ++ [("isAlpha",       show c, check SC.isAlphaL1       C.isAlpha       c) | c <- cs]
                      ++ [("isAlphaNum",    show c, check SC.isAlphaNumL1    C.isAlphaNum    c) | c <- cs]
                      ++ [("isPrint",       show c, check SC.isPrintL1       C.isPrint       c) | c <- cs]
                      ++ [("isDigit",       show c, check SC.isDigit         C.isDigit       c) | c <- cs]
                      ++ [("isOctDigit",    show c, check SC.isOctDigit      C.isOctDigit    c) | c <- cs]
                      ++ [("isHexDigit",    show c, check SC.isHexDigit      C.isHexDigit    c) | c <- cs]
                      ++ [("isLetter",      show c, check SC.isLetterL1      C.isLetter      c) | c <- cs]
                      ++ [("isMark",        show c, check SC.isMarkL1        C.isMark        c) | c <- cs]
                      ++ [("isNumber",      show c, check SC.isNumberL1      C.isNumber      c) | c <- cs]
                      ++ [("isPunctuation", show c, check SC.isPunctuationL1 C.isPunctuation c) | c <- cs]
                      ++ [("isSymbol",      show c, check SC.isSymbolL1      C.isSymbol      c) | c <- cs]
                      ++ [("isSeparator",   show c, check SC.isSeparatorL1   C.isSeparator   c) | c <- cs]
                      ++ [("isAscii",       show c, check SC.isAscii         C.isAscii       c) | c <- cs]
                      ++ [("isLatin1",      show c, check SC.isLatin1        C.isLatin1      c) | c <- cs]
                      ++ [("isAsciiUpper",  show c, check SC.isAsciiUpper    C.isAsciiUpper  c) | c <- cs]
                      ++ [("isAsciiLower",  show c, check SC.isAsciiLower    C.isAsciiLower  c) | c <- cs]
  where digitToIntRange   = (`elem` "0123456789abcdefABCDEF")
        cord :: Char -> Integer
        cord = fromIntegral . C.ord
        dig2Int :: Char -> Integer
        dig2Int = fromIntegral . C.digitToInt
        int2Dig :: Integer -> Char
        int2Dig = C.intToDigit . fromIntegral
        mkTest (nm, x, t) = testCase ("genChars-" ++ nm ++ "." ++ x) (assert t)
        check sop cop arg = case unliteral (sop (literal arg)) of
                              Nothing -> False
                              Just x  -> x == cop arg

genStrings :: [TestTree]
genStrings = map mkTest1 (  [("length",        show s,                   check1 SL.length        strLen        s      ) | s <- ss                                                       ]
                         ++ [("null",          show s,                   check1 SL.null          null          s      ) | s <- ss                                                       ]
                         ++ [("head",          show s,                   check1 SL.head          head          s      ) | s <- ss, not (null s)                                         ]
                         ++ [("tail",          show s,                   check1 SL.tail          tail          s      ) | s <- ss, not (null s)                                         ]
                         ++ [("singleton",     show c,                   check1 SL.singleton     (: [])        c      ) | c <- cs                                                       ]
                         ++ [("implode",       show s,                   checkI SL.implode                     s      ) | s <- ss                                                       ]
                         ++ [("strToNat",      show s,                   check1 SL.strToNat      strToNat      s      ) | s <- ss                                                       ]
                         ++ [("natToStr",      show i,                   check1 SL.natToStr      natToStr      i      ) | i <- iUBs                                                     ])
          ++ map mkTest2 (  [("strToCharAt",   show s, show i,           check2 SL.elemAt        strToCharAt   s i    ) | s <- ss, i  <- range s                                        ]
                         ++ [("concat",        show s, show s1,          check2 (SL.++)          (++)          s s1   ) | s <- ss, s1 <- ss                                             ]
                         ++ [("isInfixOf",     show s, show s1,          check2 SL.isInfixOf     isInfixOf     s s1   ) | s <- ss, s1 <- ss                                             ]
                         ++ [("isSuffixOf",    show s, show s1,          check2 SL.isSuffixOf    isSuffixOf    s s1   ) | s <- ss, s1 <- ss                                             ]
                         ++ [("isPrefixOf",    show s, show s1,          check2 SL.isPrefixOf    isPrefixOf    s s1   ) | s <- ss, s1 <- ss                                             ]
                         ++ [("take",          show s, show i,           check2 SL.take          genericTake   i s    ) | s <- ss, i <- iUBs                                            ]
                         ++ [("drop",          show s, show i,           check2 SL.drop          genericDrop   i s    ) | s <- ss, i <- iUBs                                            ]
                         ++ [("indexOf",       show s, show s1,          check2 SL.indexOf       indexOf       s s1   ) | s <- ss, s1 <- ss                                             ])
          ++ map mkTest3 (  [("subStr",        show s, show  i, show j,  check3 SL.subList       subStr        s i  j ) | s <- ss, i  <- range s, j <- range s, i + j <= genericLength s]
                         ++ [("replace",       show s, show s1, show s2, check3 SL.replace       replace       s s1 s2) | s <- ss, s1 <- ss, s2 <- ss                                   ]
                         ++ [("offsetIndexOf", show s, show s1, show i,  check3 SL.offsetIndexOf offsetIndexOf s s1 i ) | s <- ss, s1 <- ss, i <- range s                               ])
  where strLen :: String -> Integer
        strLen = fromIntegral . length

        strToNat :: String -> Integer
        strToNat s
          | all C.isDigit s && not (null s) = read s
          | True                            = -1

        natToStr :: Integer -> String
        natToStr i
          | i >= 0 = show i
          | True   = ""

        range :: String -> [Integer]
        range s = map fromIntegral [0 .. length s - 1]

        indexOf :: String -> String -> Integer
        indexOf s1 s2 = go 0 s1
          where go i x
                 | s2 `isPrefixOf` x = i
                 | True              = case x of
                                          "" -> -1
                                          (_:r) -> go (i+1) r

        strToCharAt :: String -> Integer -> Char
        s `strToCharAt` i = s `genericIndex` i

        subStr :: String -> Integer -> Integer -> String
        subStr s i j = genericTake j (genericDrop i s)

        replace :: String -> String -> String -> String
        replace s "" y = y ++ s
        replace s x  y = go s
          where go "" = ""
                go h@(c:rest) | x `isPrefixOf` h = y ++ drop (length x) h
                              | True             = c : go rest

        offsetIndexOf :: String -> String -> Integer -> Integer
        offsetIndexOf x y i = case indexOf (genericDrop i x) y of
                                -1 -> -1
                                r  -> r+i

        mkTest1 (nm, x, t)       = testCase ("genStrings-" ++ nm ++ "." ++ x)                         (assert t)
        mkTest2 (nm, x, y, t)    = testCase ("genStrings-" ++ nm ++ "." ++ x ++ "_" ++ y)             (assert t)
        mkTest3 (nm, x, y, z, t) = testCase ("genStrings-" ++ nm ++ "." ++ x ++ "_" ++ y ++ "_" ++ z) (assert t)

        checkI sop s = case unliteral (sop (map literal s)) of
                         Nothing -> False
                         Just x  -> s == x

        check1 sop cop arg            = case unliteral (sop (literal arg)) of
                                          Nothing -> False
                                          Just x  -> x == cop arg
        check2 sop cop arg1 arg2      = case unliteral (sop (literal arg1) (literal arg2)) of
                                          Nothing -> False
                                          Just x  -> x == cop arg1 arg2
        check3 sop cop arg1 arg2 arg3 = case unliteral (sop (literal arg1) (literal arg2) (literal arg3)) of
                                          Nothing -> False
                                          Just x  -> x == cop arg1 arg2 arg3

genLists :: [TestTree]
genLists = map mkTest1 (   [("length",        show l,                   check1 SL.length        llen          l      ) | l <- sl                                                       ]
                        ++ [("null",          show l,                   check1 SL.null          null          l      ) | l <- sl                                                       ]
                        ++ [("head",          show l,                   check1 SL.head          head          l      ) | l <- sl, not (null l)                                         ]
                        ++ [("tail",          show l,                   check1 SL.tail          tail          l      ) | l <- sl, not (null l)                                         ]
                        ++ [("singleton",     show i,                   check1 SL.singleton     (: [])        i      ) | i <- iUBs                                                     ]
                        ++ [("implode",       show l,                   checkI SL.implode       id            l      ) | l <- sl                                                       ]
                        ++ [("concat",        show l,                   check1 SL.concat        concat        l      ) | l <- sll                                                      ]
                       )
        ++ map mkTest2 (   [("listToListAt",  show l, show i,           check2 SL.listToListAt  listToListAt  l i    ) | l <- sl, i  <- range l                                        ]
                        ++ [("elemAt",        show l, show i,           check2 SL.elemAt        elemAt        l i    ) | l <- sl, i  <- range l                                        ]
                        ++ [("append",        show l, show l1,          check2 (SL.++)          (++)          l l1   ) | l <- sl, l1 <- sl                                             ]
                        ++ [("isInfixOf",     show l, show l1,          check2 SL.isInfixOf     isInfixOf     l l1   ) | l <- sl, l1 <- sl                                             ]
                        ++ [("isSuffixOf",    show l, show l1,          check2 SL.isSuffixOf    isSuffixOf    l l1   ) | l <- sl, l1 <- sl                                             ]
                        ++ [("isPrefixOf",    show l, show l1,          check2 SL.isPrefixOf    isPrefixOf    l l1   ) | l <- sl, l1 <- sl                                             ]
                        ++ [("take",          show l, show i,           check2 SL.take          genericTake   i l    ) | l <- sl, i <- iUBs                                            ]
                        ++ [("drop",          show l, show i,           check2 SL.drop          genericDrop   i l    ) | l <- sl, i <- iUBs                                            ]
                        ++ [("indexOf",       show l, show l1,          check2 SL.indexOf       indexOf       l l1   ) | l <- sl, l1 <- sl                                             ])
        ++ map mkTest3 (   [("subList",       show l, show  i, show j,  check3 SL.subList       subList       l i  j ) | l <- sl, i  <- range l, j <- range l, i + j <= genericLength l]
                        ++ [("replace",       show l, show l1, show l2, check3 SL.replace       replace       l l1 l2) | l <- sl, l1 <- sl, l2 <- sl                                   ]
                        ++ [("offsetIndexOf", show l, show l1, show i,  check3 SL.offsetIndexOf offsetIndexOf l l1 i ) | l <- sl, l1 <- sl, i <- range l                               ])
  where llen :: [Integer] -> Integer
        llen = fromIntegral . length

        range :: [Integer] -> [Integer]
        range l = map fromIntegral [0 .. length l - 1]

        indexOf :: [Integer] -> [Integer] -> Integer
        indexOf s1 s2 = go 0 s1
          where go i x
                 | s2 `isPrefixOf` x = i
                 | True              = case x of
                                          []    -> -1
                                          (_:r) -> go (i+1) r

        listToListAt :: [Integer] -> Integer -> [Integer]
        s `listToListAt` i = [s `elemAt` i]

        elemAt :: [Integer] -> Integer -> Integer
        l `elemAt` i = l `genericIndex` i

        subList :: [Integer] -> Integer -> Integer -> [Integer]
        subList s i j = genericTake j (genericDrop i s)

        replace :: [Integer] -> [Integer] -> [Integer] -> [Integer]
        replace s [] y = y ++ s
        replace s x  y = go s
          where go [] = []
                go h@(c:rest) | x `isPrefixOf` h = y ++ drop (length x) h
                              | True             = c : go rest

        offsetIndexOf :: [Integer] -> [Integer] -> Integer -> Integer
        offsetIndexOf x y i = case indexOf (genericDrop i x) y of
                                -1 -> -1
                                r  -> r+i

        mkTest1 (nm, x, t)       = testCase ("genLists-" ++ nm ++ "." ++ x)                         (assert t)
        mkTest2 (nm, x, y, t)    = testCase ("genLists-" ++ nm ++ "." ++ x ++ "_" ++ y)             (assert t)
        mkTest3 (nm, x, y, z, t) = testCase ("genLists-" ++ nm ++ "." ++ x ++ "_" ++ y ++ "_" ++ z) (assert t)

        checkI sop cop arg = case unliteral (sop (map literal arg)) of
                               Nothing -> False
                               Just x  -> x == cop arg

        check1 sop cop arg            = case unliteral (sop (literal arg)) of
                                          Nothing -> False
                                          Just x  -> x == cop arg

        check2 sop cop arg1 arg2      = case unliteral (sop (literal arg1) (literal arg2)) of
                                          Nothing -> False
                                          Just x  -> x == cop arg1 arg2

        check3 sop cop arg1 arg2 arg3 = case unliteral (sop (literal arg1) (literal arg2) (literal arg3)) of
                                          Nothing -> False
                                          Just x  -> x == cop arg1 arg2 arg3

-- Test these with make test TGT=enum_
genEnums :: [TestTree]
genEnums =
    -- Only bounded for from, otherwise infinite (or too big for chars, so subset)
    [mkTest1 "from"       s     (eq [s..    ] [sEnum|literal s..                    |]) | s <- univ @(WordN 4)]
 ++ [mkTest1 "from"       s     (eq [s..    ] [sEnum|literal s..                    |]) | s <- univ @(IntN  4)]
 ++ [mkTest1 "from"       s     (eq [s..    ] [sEnum|literal s..                    |]) | s <- w8s]
 ++ [mkTest1 "from"       s     (eq [s..    ] [sEnum|literal s..                    |]) | s <- i8s]
 ++ [mkTest1 "from"       s     (eq [s..    ] [sEnum|literal s..                    |]) | s <- hiLCS]

 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- univ @(WordN 4), t <- univ @(WordN 4)]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- univ @(IntN  4), t <- univ @(IntN  4)]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- w8s            , t <- w8s            ]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- i8s            , t <- i8s            ]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- ints           , t <- ints           ]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- floats         , t <- floats         ]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- doubles        , t <- doubles        ]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- fps            , t <- fps            ]
 ++ [mkTest2 "fromTo"     s t   (eq [s..t   ] [sEnum|literal s..literal t           |]) | s <- lcs            , t <- lcs            ]

    -- Only bounded for fromThen, otherwise infinite (or too big for chars, so subset)
 ++ [mkTest2 "fromThen"   s t   (eq [s, t.. ] [sEnum|literal s, literal t..         |]) | s <- univ @(WordN 4), t <- univ @(WordN 4), s /= t]
 ++ [mkTest2 "fromThen"   s t   (eq [s, t.. ] [sEnum|literal s, literal t..         |]) | s <- univ @(IntN  4), t <- univ @(IntN  4), s /= t]
 ++ [mkTest2 "fromThen"   s t   (eq [s, t.. ] [sEnum|literal s, literal t..         |]) | s <- w8s            , t <- w8s            , s /= t]
 ++ [mkTest2 "fromThen"   s t   (eq [s, t.. ] [sEnum|literal s, literal t..         |]) | s <- i8s            , t <- i8s            , s /= t]
 ++ [mkTest2 "fromThen"   s t   (eq [s, t.. ] [sEnum|literal s, literal t..         |]) | s <- hiLCS          , t <- hiLCS          , s <  t]

 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- univ @(WordN 4), t <- univ @(WordN 4), s /= t, u <- univ @(WordN 4)]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- univ @(IntN  4), t <- univ @(IntN  4), s /= t, u <- univ @(IntN  4)]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- w8s            , t <- w8s            , s /= t, u <- w8s            ]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- i8s            , t <- i8s            , s /= t, u <- i8s            ]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- ints           , t <- ints           , s /= t, u <- ints           ]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- floats         , t <- floats         , s /= t, u <- floats         ]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- doubles        , t <- doubles        , s /= t, u <- doubles        ]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- fps            , t <- fps            , s /= t, u <- fps            ]
 ++ [mkTest3 "fromThenTo" s t u (eq [s, t..u] [sEnum|literal s, literal t..literal u|]) | s <- lcs            , t <- lcs            , s /= t, u <- lcs            ]

  where mkTest1 pre a     = testCase ("enum_" ++ pre ++ "_|" ++ show (kindOf a) ++ "|_" ++ show a)
        mkTest2 pre a b   = testCase ("enum_" ++ pre ++ "_|" ++ show (kindOf a) ++ "|_" ++ show (a, b))
        mkTest3 pre a b c = testCase ("enum_" ++ pre ++ "_|" ++ show (kindOf a) ++ "|_" ++ show (a, b, c))

        eq c s = assert (Just c == unliteral s)

        univ :: (Enum n, Bounded n) => [n]
        univ = [minBound .. maxBound]

        ints :: [Integer]
        ints = [-3 .. 3]

        floats :: [Float]
        floats = [-3.4       .. 3.5]
        -- floats = [-3.4, -3.2 .. 3.5]    -- FAILS

        doubles :: [Double]
        doubles = [-3.4       .. 3.5]
        -- doubles = [-3.4, -3.2 .. 3.5]   -- FAILS

        fps :: [FloatingPoint 5 4]
        fps = [-3.4       .. 3.5]
        -- fps = [-3.4, -3.2 .. 3.5]  -- FAILS

        -- don't add min/max bounds here. causes too big lists.
        lcs :: [Char]
        lcs = map C.chr [5, 10, 30, 40, 41, 42, 43, 90, 100]

        -- This is the upper end of the chars, so when we test upper-bound we go quick
        hiLCS :: [Char]
        hiLCS = ['\1114105' ..]

-- Concrete test data
xsUnsigned :: (Num a, Bounded a) => [a]
xsUnsigned = take 5 (iterate (1+) minBound) ++ take 5 (iterate (\x -> x-1) maxBound)

xsSigned :: (Num a, Enum a, Bounded a) => [a]
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

-- Currently we test over all latin-1 characters. Maybe we should add some unicode here. Oh well.
cs :: String
cs = map C.chr [0..255]

-- Ditto for strings, just a few things
ss :: [String]
ss = ["", "palTRY", "teSTing", "SBV", "sTRIngs", "123", "surely", "thIS", "hI", "ly", "0"]

-- Lists are the worst in coverage!
sl :: [[Integer]]
sl = [[], [0], [-1, 1], [-10, 0, 10], [3, 4, 5, 4, 5, 3]]

-- Like wise, list of lists
sll :: [[[Integer]]]
sll = [[x, x, x] | x <- [[], [0], [-1, 1], [-10, 0, 10], [3, 4, 5, 4, 5, 3]]]

{- HLint ignore module "Reduce duplication" -}
