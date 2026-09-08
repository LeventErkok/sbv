-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.ExactNumbers
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compile-and-run tests for GMP-backed exact integer and real C lowering.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.ExactNumbers (tests) where

import Data.List                 (isInfixOf)
import Numeric                   (showHex)
import System.Exit               (ExitCode(..))
import System.FilePath           ((</>))
import System.IO.Temp            (withSystemTempDirectory)
import System.Process            (readProcessWithExitCode)
import Test.Tasty.HUnit          (assertBool, assertEqual)

import Data.SBV.Internals

import Utils.SBVTestFramework

-- | GMP-backed exact-number C backend tests.
tests :: TestTree
tests = testGroup "CodeGeneration.ExactNumbers"
  [ testCase "compile and execute unbounded arithmetic" exactIntegerArithmetic
  , testCase "compile and execute Euclidean division" exactIntegerDivision
  , testCase "compile and execute native conversions" exactNativeConversions
  , testCase "compile and execute wide conversions" exactWideConversions
  , testCase "compile and execute wide real conversions" exactWideRealConversions
  , testCase "compile and execute rational arithmetic" exactRealArithmetic
  , testCase "compile and execute an exact-number library" exactNumberLibrary
  ]

-- | Exercise arithmetic well beyond any native or wide fixed-width integer.
exactIntegerArithmetic :: Assertion
exactIntegerArithmetic = withSystemTempDirectory "sbv-exact-integer" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [x, y]
        a <- cgInput "a" :: SBVCodeGen SInteger
        b <- cgInput "b" :: SBVCodeGen SInteger
        let added     = a + b
            result    = abs (added * (a - b))
            bitResult = (added `xor` a) .&. complement b
            selected  = ite (a .> b) result (negate result)
        cgOutput "added" added
        cgOutput "bitResult" bitResult
        cgReturn selected
      x           = 2 ^ (700 :: Int) + 123456789
      y           = negate (2 ^ (511 :: Int)) + 987654321
      expected    = abs ((x + y) * (x - y))
      expectedBit = ((x + y) `xor` x) .&. complement y
  compileAndRunGMP dir "exactIntegerArithmetic" program [show expected, show (x + y), show expectedBit]

-- | Exercise SMT-Lib Euclidean quotient and nonnegative remainder semantics.
exactIntegerDivision :: Assertion
exactIntegerDivision = withSystemTempDirectory "sbv-exact-integer-division" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [-20, -6]
        a <- cgInput "a" :: SBVCodeGen SInteger
        b <- cgInput "b" :: SBVCodeGen SInteger
        let quotient  = a `sEDiv` b
            remainder = a `sEMod` b
        cgOutput "quotient" quotient
        cgOutput "remainder" remainder
        cgReturn (quotient .== 4 .&& remainder .== 4)
  compileAndRunGMP dir "exactIntegerDivision" program ["= 1", "quotient =4", "remainder =4"]

-- | Exercise exact conversions to and from native signed and unsigned words.
exactNativeConversions :: Assertion
exactNativeConversions = withSystemTempDirectory "sbv-exact-native-conversions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [maxWord, minInt]
        unsignedValue <- cgInput "unsignedValue" :: SBVCodeGen SWord64
        signedValue   <- cgInput "signedValue"   :: SBVCodeGen SInt64
        let exactUnsigned = sFromIntegral unsignedValue :: SInteger
            exactSigned   = sFromIntegral signedValue :: SInteger
            wrapped       = sFromIntegral (exactUnsigned + 1) :: SWord64
            asReal        = sFromIntegral signedValue :: SReal
        cgOutput "wrapped" wrapped
        cgOutput "asReal" asReal
        cgReturn (exactUnsigned + exactSigned)
      maxWord  = 2 ^ (64 :: Int) - 1
      minInt   = negate (2 ^ (63 :: Int))
      expected = 2 ^ (63 :: Int) - 1 :: Integer
  compileAndRunGMP dir "exactNativeConversions" program [show expected, "wrapped = 0x0000000000000000ULL", "asReal =-9223372036854775808"]

-- | Exercise signed and unsigned conversions between GMP integers and
-- limb-backed bit-vectors in both directions.
exactWideConversions :: Assertion
exactWideConversions = withSystemTempDirectory "sbv-exact-wide-conversions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [unsignedSample, signedSample, exactSample]
        unsignedValue <- cgInput "unsignedValue" :: SBVCodeGen (SWord 673)
        signedValue   <- cgInput "signedValue"   :: SBVCodeGen (SInt 673)
        exactValue    <- cgInput "exactValue"    :: SBVCodeGen SInteger
        let exactUnsigned     = sFromIntegral unsignedValue :: SInteger
            exactSigned       = sFromIntegral signedValue :: SInteger
            unsignedRoundTrip = (sFromIntegral exactUnsigned :: SWord 673) .== unsignedValue
            signedRoundTrip   = (sFromIntegral exactSigned :: SInt 673) .== signedValue
            wrappedUnsigned   = sFromIntegral exactValue :: SWord 673
            wrappedSigned     = sFromIntegral exactValue :: SInt 673
        cgOutput "unsignedRoundTrip" unsignedRoundTrip
        cgOutput "signedRoundTrip" signedRoundTrip
        cgOutput "wrappedUnsigned" wrappedUnsigned
        cgOutput "wrappedSigned" wrappedSigned
        cgReturn (exactUnsigned + exactSigned)
      unsignedSample = 2 ^ (672 :: Int) + 0x123456789abcdef
      signedSample   = negate (2 ^ (671 :: Int)) + 0xfedcba987654321
      exactSample    = negate (2 ^ (700 :: Int)) + 0x112233445566778899
      expected       = unsignedSample + signedSample
      wrapped        = exactSample `mod` 2 ^ (673 :: Int)
  compileAndRunGMP dir "exactWideConversions" program
    [ show expected
    , "unsignedRoundTrip = 1"
    , "signedRoundTrip = 1"
    , "wrappedUnsigned =" ++ asHex 11 wrapped
    , "wrappedSigned =" ++ asHex 11 wrapped
    ]

-- | Exercise exact conversion of signed and unsigned limb-backed values to
-- rational reals, followed by explicit floor and truncation back to wide
-- bit-vectors through 'SInteger'.
exactWideRealConversions :: Assertion
exactWideRealConversions = withSystemTempDirectory "sbv-exact-wide-real-conversions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [unsignedSample, signedSample]
        unsignedValue <- cgInput "unsignedValue" :: SBVCodeGen (SWord 673)
        signedValue   <- cgInput "signedValue"   :: SBVCodeGen (SInt 673)
        let unsignedReal = sFromIntegral unsignedValue :: SReal
            signedReal   = sFromIntegral signedValue :: SReal
            fraction     = signedReal / 3
            floorWide    = sFromIntegral (sRealToSIntegerFloor fraction) :: SInt 673
            truncateWide = sFromIntegral (sRealToSIntegerTruncate fraction) :: SInt 673
        cgOutput "unsignedReal" unsignedReal
        cgOutput "signedReal" signedReal
        cgOutput "fraction" fraction
        cgOutput "floorWide" floorWide
        cgOutput "truncateWide" truncateWide
        cgReturn (unsignedReal + signedReal)
      unsignedSample = 2 ^ (672 :: Int) + 0x123456789abcdef
      signedSample   = negate (2 ^ (671 :: Int)) + 0xfedcba987654321
      floorResult    = signedSample `div` 3
      truncateResult = signedSample `quot` 3
      modulus        = 2 ^ (673 :: Int)
  compileAndRunGMP dir "exactWideRealConversions" program
    [ show (unsignedSample + signedSample)
    , "unsignedReal =" ++ show unsignedSample
    , "signedReal =" ++ show signedSample
    , "fraction =" ++ show signedSample ++ "/3"
    , "floorWide =" ++ asHex 11 (floorResult `mod` modulus)
    , "truncateWide =" ++ asHex 11 (truncateResult `mod` modulus)
    ]

-- | Exercise exact rational arithmetic and integer-to-real conversion.
exactRealArithmetic :: Assertion
exactRealArithmetic = withSystemTempDirectory "sbv-exact-real" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5, 2, 2]
        a <- cgInput "a" :: SBVCodeGen SReal
        b <- cgInput "b" :: SBVCodeGen SReal
        integer <- cgInput "integer" :: SBVCodeGen SInteger
        let converted = sFromIntegral integer :: SReal
            base      = a / 3 + b / 7 + converted
            result    = ite (a .> b) (abs (base * (-3))) 0
        cgOutput "converted" converted
        cgOutput "base" base
        cgReturn result
  compileAndRunGMP dir "exactRealArithmetic" program ["83/7", "converted =2", "base =83/21"]

-- | Exercise merged headers, archives, and drivers for exact-number libraries.
exactNumberLibrary :: Assertion
exactNumberLibrary = withSystemTempDirectory "sbv-exact-library" $ \dir -> do
  let integerProgram = do
        cgOverwriteFiles True
        cgSetDriverValues [2 ^ (130 :: Int)]
        value <- cgInput "value" :: SBVCodeGen SInteger
        cgReturn (value + 7)
      realProgram = do
        cgOverwriteFiles True
        cgSetDriverValues [5]
        value <- cgInput "value" :: SBVCodeGen SReal
        cgReturn (value / 3)
      wideProgram = do
        cgOverwriteFiles True
        cgSetDriverValues [wideSample]
        value <- cgInput "value" :: SBVCodeGen (SInt 673)
        cgReturn (sFromIntegral value :: SInteger)
      wideSample = negate (2 ^ (670 :: Int)) + 12345

  (_, cfg, bundle) <- compileToCLib' "exactNumberLibrary"
    [ ("integerPart", integerProgram)
    , ("realPart", realProgram)
    , ("widePart", wideProgram)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)

  (makeExit, _, makeError) <- readProcessWithExitCode "make" ["-C", dir] ""
  assertEqual makeError ExitSuccess makeExit

  let driverExecutable = dir </> "exactNumberLibrary_driver"
  (runExit, stdoutText, runError) <- readProcessWithExitCode driverExecutable [] ""
  assertEqual runError ExitSuccess runExit
  assertOutput stdoutText (show (2 ^ (130 :: Int) + 7 :: Integer))
  assertOutput stdoutText "5/3"
  assertOutput stdoutText (show wideSample)

-- | Generate, compile, and execute a program against the system GMP package.
compileAndRunGMP :: FilePath -> String -> SBVCodeGen () -> [String] -> Assertion
compileAndRunGMP dir functionName program expected = do
  (_, cfg, bundle) <- compileToC' functionName program
  renderCgPgmBundle (Just dir) (cfg, bundle)

  (pkgExit, pkgOutput, pkgError) <- readProcessWithExitCode "pkg-config" ["--cflags", "--libs", "gmp"] ""
  assertEqual pkgError ExitSuccess pkgExit

  let source = dir </> functionName ++ ".c"
      driver = dir </> functionName ++ "_driver.c"
      exe    = dir </> functionName ++ "_driver"
      args   = ["-std=c11", "-Wall", "-Werror", source, driver, "-o", exe] ++ words pkgOutput
  (ccExit, _, ccError) <- readProcessWithExitCode "cc" args ""
  assertEqual ccError ExitSuccess ccExit

  (makeExit, _, makeError) <- readProcessWithExitCode "make" ["-C", dir] ""
  assertEqual makeError ExitSuccess makeExit

  (runExit, stdoutText, runError) <- readProcessWithExitCode exe [] ""
  assertEqual runError ExitSuccess runExit
  mapM_ (assertOutput stdoutText) expected

  makefile <- readFile (dir </> "Makefile")
  assertBool "Generated Makefile does not request GMP compiler flags" ("pkg-config --cflags gmp" `isInfixOf` makefile)
  assertBool "Generated Makefile does not request GMP linker flags" ("pkg-config --libs gmp" `isInfixOf` makefile)

-- | Assert that generated driver output contains an expected fragment.
assertOutput :: String -> String -> Assertion
assertOutput stdoutText fragment =
  assertBool ("Expected generated output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText)

-- | Render the fixed-limb hexadecimal form printed by generated drivers.
asHex :: Int -> Integer -> String
asHex limbCount value = "0x" ++ replicate (16 * limbCount - length rendered) '0' ++ rendered
 where rendered = showHex value ""
