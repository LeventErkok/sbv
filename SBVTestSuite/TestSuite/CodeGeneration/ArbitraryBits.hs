-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.ArbitraryBits
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compile-and-run tests for C lowering of arbitrary-width bit-vectors.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.ArbitraryBits (tests) where

import Data.List                 (isInfixOf)
import Data.Proxy                (Proxy(..))
import Numeric                   (showHex)
import System.Exit               (ExitCode(..))
import System.FilePath           ((</>))
import System.IO.Temp            (withSystemTempDirectory)
import System.Process            (readProcessWithExitCode)
import Test.Tasty.HUnit          (assertBool, assertEqual)

import Data.SBV.Internals
import Data.SBV.Tools.Overflow

import Utils.SBVTestFramework hiding ((#), bvExtract)

-- | Arbitrary-width C backend tests.
tests :: TestTree
tests = testGroup "CodeGeneration.ArbitraryBits"
  [ testCase "compile and execute 673-bit arithmetic" wide673
  , testCase "compile and execute signed 673-bit arithmetic" signed673
  , testCase "compile and execute non-aligned join/extract" joinExtract
  , testCase "compile and execute unsigned overflow predicates" unsignedOverflow
  , testCase "compile and execute signed overflow predicates" signedOverflow
  , testCase "compile and execute native overflow predicates" nativeOverflow
  , testCase "compile and execute exact native bit operations" nativeBitOperations
  , testCase "compile and execute exact native arithmetic" nativeArithmetic
  , testCase "compile and execute checked wide table lookup" wideLookup
  , testCase "compile and execute wide array keys and values" wideArray
  , testCase "compile and execute a wide callback-backed array" wideArrayInput
  , testCase "compile and execute a wide structured lambda array" wideLambdaArray
  , testCase "compile and execute a wide structured lambda table" wideLambdaTable
  , testCase "compile and execute arithmetic boundary cases" arithmeticBoundaries
  ]

-- | Exercise unsigned 673-bit arithmetic, shifts, rotation, and division.
wide673 :: Assertion
wide673 = withSystemTempDirectory "sbv-wide673" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [x, y]
        a <- cgInput "a" :: SBVCodeGen (SWord 673)
        b <- cgInput "b" :: SBVCodeGen (SWord 673)
        let symbolicResult = rotateL (((a + b) * (a - b)) `xor` shiftR a 67) 193
        cgReturn (symbolicResult `sQuot` (b + 1))
  compileAndRun dir "wide673" program (asHex 11 result)
 where w                 = 673
       modulus           = 2 ^ w
       mask              = modulus - 1
       x                 = 2 ^ (672 :: Int) + 9
       y                 = 17
       add a b           = (a + b) .&. mask
       sub a b           = (a - b) .&. mask
       mul a b           = (a * b) .&. mask
       shr a n           = a `shiftR` n
       rotl a n          = let r = n `mod` w in ((a `shiftLInteger` r) .|. (a `shiftR` (w - r))) .&. mask
       expectedZ         = rotl (mul (add x y) (sub x y) `xor` shr x 67) 193
       result            = expectedZ `quot` add y 1
       shiftLInteger a n = a * (2 ^ n)

-- | Exercise signed 673-bit ordering, quotient, remainder, and arithmetic shift.
signed673 :: Assertion
signed673 = withSystemTempDirectory "sbv-signed673" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [x, y]
        a <- cgInput "a" :: SBVCodeGen (SInt 673)
        b <- cgInput "b" :: SBVCodeGen (SInt 673)
        let q = a `sQuot` b
            r = a `sRem` b
        cgReturn $ ite (a .< b) (q + r) (shiftR a 130)
  compileAndRun dir "signed673" program (asHex 11 expectedRaw)
 where modulus     = 2 ^ (673 :: Int)
       x           = negate (2 ^ (671 :: Int)) + 12345
       y           = -17
       expectedRaw = ((x `quot` y) + (x `rem` y)) `mod` modulus

-- | Exercise non-aligned concatenation and extraction across limb boundaries.
joinExtract :: Assertion
joinExtract = withSystemTempDirectory "sbv-join-extract" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [hi, lo]
        a <- cgInput "high" :: SBVCodeGen (SWord 337)
        b <- cgInput "low"  :: SBVCodeGen (SWord 336)
        let joined = a # b :: SWord 673
        cgReturn (bvExtract (Proxy @511) (Proxy @128) joined :: SWord 384)
  compileAndRun dir "joinExtract" program (asHex 6 expected)
 where hi             = 2 ^ (336 :: Int) + 0x123456789abcdef
       lo             = 2 ^ (335 :: Int) + 0xfedcba987654321
       expectedJoined = hi * 2 ^ (336 :: Int) + lo
       expected       = (expectedJoined `shiftR` 128) .&. (2 ^ (384 :: Int) - 1)

-- | Exercise unsigned overflow and underflow predicates at a non-native width.
unsignedOverflow :: Assertion
unsignedOverflow = withSystemTempDirectory "sbv-unsigned-overflow" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2 ^ (65 :: Int) - 1, 2]
        a <- cgInput "a" :: SBVCodeGen (SWord 65)
        b <- cgInput "b" :: SBVCodeGen (SWord 65)
        cgReturn $ pack [bvAddO a b, bvSubO 0 b, bvMulO a b, bvMulO b 3]
  compileAndRun dir "unsignedOverflow" program (asHex 2 7)
 where pack :: [SBool] -> SWord 65
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8])

-- | Exercise signed overflow predicates, including both signed extrema.
signedOverflow :: Assertion
signedOverflow = withSystemTempDirectory "sbv-signed-overflow" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2 ^ (64 :: Int) - 1, 1]
        a <- cgInput "a" :: SBVCodeGen (SInt 65)
        b <- cgInput "b" :: SBVCodeGen (SInt 65)
        let minValue = fromInteger (negate (2 ^ (64 :: Int))) :: SInt 65
        cgReturn $ pack [bvAddO a b, bvSubO minValue b, bvMulO a (b + b), bvDivO minValue (negate b), bvNegO minValue, bvMulO a b]
  compileAndRun dir "signedOverflow" program (asHex 2 31)
 where pack :: [SBool] -> SWord 65
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32])

-- | Exercise every unsigned and signed overflow predicate at native C widths,
-- including promotion-sensitive 8-bit and undefined-in-C 64-bit boundaries.
nativeOverflow :: Assertion
nativeOverflow = withSystemTempDirectory "sbv-native-overflow" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [maxWord, 2, maxInt, 1, minInt, minInt8]
        unsignedMax <- cgInput "unsignedMax" :: SBVCodeGen SWord64
        unsignedTwo <- cgInput "unsignedTwo" :: SBVCodeGen SWord64
        signedMax   <- cgInput "signedMax"   :: SBVCodeGen SInt64
        signedOne   <- cgInput "signedOne"   :: SBVCodeGen SInt64
        signedMin   <- cgInput "signedMin"   :: SBVCodeGen SInt64
        signedMin8  <- cgInput "signedMin8"  :: SBVCodeGen SInt8
        let flags = [ bvAddO unsignedMax unsignedTwo
                    , bvSubO 0 unsignedTwo
                    , bvMulO unsignedMax unsignedTwo
                    , bvMulO unsignedTwo 3
                    , bvAddO signedMax signedOne
                    , bvSubO signedMin signedOne
                    , bvMulO signedMax 2
                    , bvDivO signedMin (negate signedOne)
                    , bvNegO signedMin
                    , bvMulO signedMax signedOne
                    , bvNegO signedMin8
                    , bvMulO signedMin8 (-1)
                    ]
        cgReturn $ pack flags
      maxWord = 2 ^ (64 :: Int) - 1
      maxInt  = 2 ^ (63 :: Int) - 1
      minInt  = negate (2 ^ (63 :: Int))
      minInt8 = -128
  compileAndRun dir "nativeOverflow" program "0x0df7U"
 where pack :: [SBool] -> SWord16
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048])

-- | Exercise non-byte-aligned native extraction and signed rotations,
-- including counts larger than the operand width and SBV's unchanged result
-- for a negative constant count.
nativeBitOperations :: Assertion
nativeBitOperations = withSystemTempDirectory "sbv-native-bit-operations" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [wordSample, signedSample]
        wordValue   <- cgInput "wordValue"   :: SBVCodeGen (SWord 32)
        signedValue <- cgInput "signedValue" :: SBVCodeGen (SInt 32)
        let extracted    = bvExtract (Proxy @10) (Proxy @3) wordValue :: SWord 8
            highHalf     = bvExtract (Proxy @31) (Proxy @16) wordValue :: SWord 16
            lowHalf      = bvExtract (Proxy @15) (Proxy @0) wordValue :: SWord 16
            rejoined     = highHalf # lowHalf :: SWord 32
            signExtended = signExtend signedValue :: SInt 64
            zeroExtended = zeroExtend wordValue :: SWord 64
            narrowed     = sFromIntegral signedValue :: SWord8
            shiftedLeft  = signed32 (raw32 (raw32 signedSample * 2 ^ (3 :: Int)))
            shiftedRight = signedSample `div` 2 ^ (3 :: Int)
            flags        = [ extracted .== fromInteger extractedExpected
                           , rotateL signedValue 37   .== fromInteger rotatedLeftExpected
                           , rotateR signedValue 39   .== fromInteger rotatedRightExpected
                           , rotateR signedValue (-5) .== signedValue
                           , signExtended .== fromInteger signedSample
                           , zeroExtended .== fromInteger wordSample
                           , narrowed .== fromInteger (raw32 signedSample `mod` 2 ^ (8 :: Int))
                           , rejoined .== wordValue
                           , shiftL signedValue 3  .== fromInteger shiftedLeft
                           , shiftR signedValue 3  .== fromInteger shiftedRight
                           , shiftL signedValue 32 .== 0
                           , shiftR signedValue 32 .== (-1)
                           ]
        cgReturn $ pack flags
  compileAndRun dir "nativeBitOperations" program "0x0fffU"
 where wordSample :: Integer
       wordSample           = 0xdeadbeef

       signedSample :: Integer
       signedSample         = -19088744

       extractedExpected :: Integer
       extractedExpected    = (wordSample `div` (2 ^ (3 :: Int))) `mod` (2 ^ (8 :: Int))

       rotatedLeftExpected :: Integer
       rotatedLeftExpected  = signed32 (rotateLeft32 signedSample 5)

       rotatedRightExpected :: Integer
       rotatedRightExpected = signed32 (rotateRight32 signedSample 7)

       rotateLeft32 :: Integer -> Int -> Integer
       rotateLeft32 value amount = (raw32 value * 2 ^ amount + raw32 value `div` 2 ^ (32 - amount)) `mod` 2 ^ (32 :: Int)

       rotateRight32 :: Integer -> Int -> Integer
       rotateRight32 value amount = (raw32 value `div` 2 ^ amount + raw32 value * 2 ^ (32 - amount)) `mod` 2 ^ (32 :: Int)

       raw32 :: Integer -> Integer
       raw32 value = value `mod` 2 ^ (32 :: Int)

       signed32 :: Integer -> Integer
       signed32 value
         | value >= 2 ^ (31 :: Int) = value - 2 ^ (32 :: Int)
         | True                     = value

       pack :: [SBool] -> SWord16
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048])

-- | Exercise modular native arithmetic and the two division cases that would
-- otherwise be undefined in C.
nativeArithmetic :: Assertion
nativeArithmetic = withSystemTempDirectory "sbv-native-arithmetic" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [minimumInt64, -1, maximumInt64, maximumInt32, maximumWord16]
        minimum64 <- cgInput "minimum64" :: SBVCodeGen SInt64
        negative1 <- cgInput "negative1" :: SBVCodeGen SInt64
        maximum64 <- cgInput "maximum64" :: SBVCodeGen SInt64
        maximum32 <- cgInput "maximum32" :: SBVCodeGen SInt32
        maximum16 <- cgInput "maximum16" :: SBVCodeGen SWord16
        let flags = [ maximum64 + 1 .== fromInteger minimumInt64
                    , minimum64 + negative1 .== fromInteger maximumInt64
                    , minimum64 - 1 .== fromInteger maximumInt64
                    , maximum64 * 2 .== (-2)
                    , negate minimum64 .== minimum64
                    , abs minimum64 .== minimum64
                    , minimum64 `sQuot` negative1 .== minimum64
                    , minimum64 `sRem` negative1 .== 0
                    , minimum64 `sQuot` 0 .== 0
                    , minimum64 `sRem` 0 .== minimum64
                    , maximum32 * maximum32 .== 1
                    , maximum16 * maximum16 .== 1
                    ]
        cgReturn $ pack flags
  compileAndRun dir "nativeArithmetic" program "0x0fffU"
 where minimumInt64 :: Integer
       minimumInt64 = negate (2 ^ (63 :: Int))

       maximumInt64 :: Integer
       maximumInt64 = 2 ^ (63 :: Int) - 1

       maximumInt32 :: Integer
       maximumInt32 = 2 ^ (31 :: Int) - 1

       maximumWord16 :: Integer
       maximumWord16 = 2 ^ (16 :: Int) - 1

       pack :: [SBool] -> SWord16
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048])

-- | Exercise checked table lookup with both a wide index and wide elements.
wideLookup :: Assertion
wideLookup = withSystemTempDirectory "sbv-wide-lookup" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgPerformRTCs True
        cgSetDriverValues [2 ^ (64 :: Int) + 1]
        index <- cgInput "index" :: SBVCodeGen (SWord 65)
        cgReturn (select [11, 22] 99 index :: SWord 673)
  compileAndRun dir "wideLookup" program (asHex 11 99)

-- | Exercise persistent arrays whose keys and values both use exact-width
-- limb representations.
wideArray :: Assertion
wideArray = withSystemTempDirectory "sbv-wide-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [keySample, valueSample]
        key   <- cgInput "key"   :: SBVCodeGen (SWord 673)
        value <- cgInput "value" :: SBVCodeGen (SWord 257)
        let base    = constArray 3
            updated = writeArray base key value
        cgOutput "defaultRead" (readArray updated (key + 1))
        cgReturn (readArray updated key)
      keySample   = 2 ^ (672 :: Int) + 17
      valueSample = 2 ^ (256 :: Int) + 5
  compileAndRun dir "wideArray" program (asHex 5 valueSample)

-- | Exercise the public callback descriptor when both its key and returned
-- value use multi-limb bit-vector representations.
wideArrayInput :: Assertion
wideArrayInput = withSystemTempDirectory "sbv-wide-array-input" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [valueSample, keySample]
        source <- cgInput "source" :: SBVCodeGen (SArray (WordN 673) (WordN 257))
        key    <- cgInput "key"    :: SBVCodeGen (SWord 673)
        cgReturn (readArray source key)
      keySample   = 2 ^ (672 :: Int) + 17
      valueSample = 2 ^ (256 :: Int) + 5
  compileAndRun dir "wideArrayInput" program (asHex 5 valueSample)

-- | Exercise a structured array lambda whose parameter, local arithmetic,
-- and result all use the 673-bit limb representation.
wideLambdaArray :: Assertion
wideLambdaArray = withSystemTempDirectory "sbv-wide-lambda-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [keySample]
        key <- cgInput "key" :: SBVCodeGen (SWord 673)
        let source = lambdaArray (\index -> index * 3 + 5) :: SArray (WordN 673) (WordN 673)
        cgReturn (readArray source key)
      keySample = 2 ^ (672 :: Int) + 17
      expected  = (keySample * 3 + 5) `mod` (2 ^ (673 :: Int))
  compileAndRun dir "wideLambdaArray" program (asHex 11 expected)

-- | Exercise a parameter-dependent lookup table entirely within a structured
-- lambda using arbitrary-width indices, elements, and results.
wideLambdaTable :: Assertion
wideLambdaTable = withSystemTempDirectory "sbv-wide-lambda-table" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        key <- cgInput "key" :: SBVCodeGen (SWord 673)
        let source = lambdaArray (\index -> select [index + 1, index * 3] 99 index) :: SArray (WordN 673) (WordN 673)
        cgReturn (readArray source key)
  compileAndRun dir "wideLambdaTable" program (asHex 11 3)

-- | Exercise division-by-zero, extreme shifts, and signed-minimum division.
arithmeticBoundaries :: Assertion
arithmeticBoundaries = withSystemTempDirectory "sbv-arithmetic-boundaries" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [negate (2 ^ (64 :: Int))]
        a <- cgInput "a" :: SBVCodeGen (SInt 65)
        let z = 0 :: SInt 65
        cgReturn $ pack [a `sQuot` z .== z
                        , a `sRem` z .== a
                        , shiftL a 65 .== z
                        , shiftR a 65 .== (-1)
                        , a `sQuot` (-1) .== a
                        , a `sRem` (-1) .== z
                        , rotateL a 66 .== 1]
  compileAndRun dir "arithmeticBoundaries" program (asHex 2 127)
 where pack :: [SBool] -> SWord 65
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32, 64])

-- | Generate, compile, and execute a C program, checking its encoded result.
compileAndRun :: FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRun dir functionName program expected = do
  (_, cfg, bundle) <- compileToC' functionName program
  renderCgPgmBundle (Just dir) (cfg, bundle)

  let source = dir </> functionName ++ ".c"
      driver = dir </> functionName ++ "_driver.c"
      exe    = dir </> functionName ++ "_driver"
  (ccExit, _, ccErr) <- readProcessWithExitCode "cc" ["-std=c11", "-Wall", "-Werror", source, driver, "-o", exe] ""
  assertEqual ccErr ExitSuccess ccExit

  (runExit, out, runErr) <- readProcessWithExitCode exe [] ""
  assertEqual runErr ExitSuccess runExit
  assertBool ("Expected generated output to contain " ++ expected ++ ", received:\n" ++ out) (expected `isInfixOf` out)

-- | Render the fixed-limb hexadecimal form printed by generated drivers.
asHex :: Int -> Integer -> String
asHex limbCount value = "0x" ++ replicate (16 * limbCount - length h) '0' ++ h
 where h = showHex value ""
