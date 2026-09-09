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

{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

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
import Data.SBV.Tuple (tuple, untuple)

import Utils.SBVTestFramework

-- | An exact-number ADT nested inside 'ExactAggregate'.
data ExactLeaf = ExactLeaf Integer AlgReal deriving Show

-- | A sum type combining nested ADT and tuple ownership.
data ExactAggregate = ExactAbsent
                    | ExactAggregate ExactLeaf (Integer, AlgReal)
                    deriving Show

-- | Generate symbolic interfaces for the exact-number ADTs.
mkSymbolic [''ExactLeaf, ''ExactAggregate]

-- | GMP-backed exact-number C backend tests.
tests :: TestTree
tests = testGroup "CodeGeneration.ExactNumbers"
  [ testCase "compile and execute unbounded arithmetic" exactIntegerArithmetic
  , testCase "compile and execute Euclidean division" exactIntegerDivision
  , testCase "compile and execute native conversions" exactNativeConversions
  , testCase "compile and execute wide conversions" exactWideConversions
  , testCase "compile and execute wide real conversions" exactWideRealConversions
  , testCase "compile and execute rational arithmetic" exactRealArithmetic
  , testCase "compile and execute exact table lookup" exactTableLookup
  , testCase "compile and execute exact array keys and values" exactArray
  , testCase "compile and execute an exact callback-backed array" exactArrayInput
  , testCase "compile and execute an exact structured lambda array" exactLambdaArray
  , testCase "compile and execute an exact structured lambda table" exactLambdaTable
  , testCase "return and output owned exact arrays" ownedExactArrays
  , testCase "use exact fields inside tuples" exactTupleFields
  , testCase "use owned exact tuples across the public ABI" ownedExactTuples
  , testCase "use owned exact ADTs across the public ABI" ownedExactADTs
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

-- | Exercise finite tables with an unbounded index and GMP-backed integer and
-- rational results, including negative and oversized default cases.
exactTableLookup :: Assertion
exactTableLookup = withSystemTempDirectory "sbv-exact-table" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgPerformRTCs True
        cgSetDriverValues [1, -1, 500, 2 ^ (200 :: Int)]
        inRangeIndex   <- cgInput "inRangeIndex"   :: SBVCodeGen SInteger
        negativeIndex  <- cgInput "negativeIndex"  :: SBVCodeGen SInteger
        oversizedIndex <- cgInput "oversizedIndex" :: SBVCodeGen SInteger
        tableValue     <- cgInput "tableValue"     :: SBVCodeGen SInteger
        let integerResult   = select [2 ^ (130 :: Int), tableValue + 7] (-11) inRangeIndex :: SInteger
            negativeResult  = select [3 / 2, 5 / 3] (7 / 4) negativeIndex :: SReal
            oversizedResult = select [13, 17] 19 oversizedIndex :: SInteger
        cgOutput "negativeResult" negativeResult
        cgOutput "oversizedResult" oversizedResult
        cgReturn integerResult
  compileAndRunGMP dir "exactTableLookup" program [show (2 ^ (200 :: Int) + 7 :: Integer), "negativeResult =7/4", "oversizedResult =19"]

-- | Exercise a persistent array with GMP-backed integer keys and rational
-- values, including a read from the unchanged base version.
exactArray :: Assertion
exactArray = withSystemTempDirectory "sbv-exact-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2 ^ (300 :: Int) + 9, 20]
        key   <- cgInput "key"   :: SBVCodeGen SInteger
        value <- cgInput "value" :: SBVCodeGen SInteger
        let stored  = sFromIntegral value / 3 :: SReal
            base    = constArray (1 / 3 :: SReal)
            updated = writeArray base key stored
        cgOutput "baseValue" (readArray base key)
        cgReturn (readArray updated key)
  compileAndRunGMP dir "exactArray" program ["20/3", "baseValue =1/3"]

-- | Exercise borrowed callback input and overlay semantics with GMP-backed
-- integer keys and rational values.
exactArrayInput :: Assertion
exactArrayInput = withSystemTempDirectory "sbv-exact-array-input" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [7, 2 ^ (300 :: Int) + 9, 20]
        source <- cgInput "source" :: SBVCodeGen (SArray Integer AlgReal)
        key    <- cgInput "key"    :: SBVCodeGen SInteger
        value  <- cgInput "value"  :: SBVCodeGen SInteger
        let updated = writeArray source key (sFromIntegral value / 3)
        cgOutput "sourceValue" (readArray source key)
        cgReturn (readArray updated key)
  compileAndRunGMP dir "exactArrayInput" program ["20/3", "sourceValue =7"]

-- | Exercise repeated reads from a structured array lambda whose arithmetic
-- allocates exact rational results in the enclosing generated-call arena.
exactLambdaArray :: Assertion
exactLambdaArray = withSystemTempDirectory "sbv-exact-lambda-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [20]
        key <- cgInput "key" :: SBVCodeGen SInteger
        let source = lambdaArray (\index -> sFromIntegral index / 3) :: SArray Integer AlgReal
        cgOutput "value" (readArray source key)
        cgReturn (readArray source (key + 1))
  compileAndRunGMP dir "exactLambdaArray" program ["7", "value =20/3"]

-- | Exercise a parameter-dependent exact table whose entries allocate in the
-- structured lambda's enclosing GMP arena.
exactLambdaTable :: Assertion
exactLambdaTable = withSystemTempDirectory "sbv-exact-lambda-table" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        key <- cgInput "key" :: SBVCodeGen SInteger
        let source = lambdaArray (\index -> select [sFromIntegral index / 3, sFromIntegral index / 5] 7 index)
                     :: SArray Integer AlgReal
        cgReturn (readArray source key)
  compileAndRunGMP dir "exactLambdaTable" program ["1/5"]

-- | Exercise exact store cloning and a structured callback that allocates
-- after the generated function's original GMP arena has been released.
ownedExactArrays :: Assertion
ownedExactArrays = withSystemTempDirectory "sbv-owned-exact-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        let source = lambdaArray (\index -> sFromIntegral index / 3) :: SArray Integer AlgReal
        cgOutput "stored" (writeArray source 0 (5 / 3))
        cgReturn source

  compileAndRunGMP dir "ownedExactArrays" program ["ownedExactArrays(&stored)[0] =0", "stored[0] =5/3"]

-- | Exercise exact tuple construction, constants in a finite table,
-- projection, and copying into scalar caller-owned results.
exactTupleFields :: Assertion
exactTupleFields = withSystemTempDirectory "sbv-exact-tuple-fields" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0]
        index <- cgInput "index" :: SBVCodeGen SWord8
        let first, second             :: SBV (AlgReal, Integer)
            first                     = tuple (1 / 3, 2 ^ (130 :: Int))
            second                    = tuple (5 / 7, 9)
            selected                  = select [first] second index
            (realValue, integerValue) = untuple selected
        cgOutput "integerValue" integerValue
        cgReturn realValue

  compileAndRunGMP dir "exactTupleFields" program ["1/3", show (2 ^ (130 :: Int) :: Integer)]

-- | Exercise borrowed exact-tuple inputs and independently owned outputs and
-- returns whose GMP fields survive the generated call's temporary arena.
ownedExactTuples :: Assertion
ownedExactTuples = withSystemTempDirectory "sbv-owned-exact-tuples" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen (SBV (Integer, (AlgReal, Integer)))
        let (integerValue, nested)      = untuple source
            (realValue, secondInteger) = untuple nested
            outputTuple                = tuple (integerValue + 1, tuple (realValue / 3, secondInteger + 2))
            result                     = tuple (integerValue * 2, tuple (realValue + 1, secondInteger * 3))
        cgOutput "output" outputTuple
        cgReturn result
      seed           = 2 ^ (130 :: Int)
      expectedOutput = "output =(" ++ show (seed + 1) ++ ", (" ++ show (seed + 1) ++ "/3, " ++ show (seed + 4) ++ "))"
      expectedReturn = "(" ++ show (seed * 2) ++ ", (" ++ show (seed + 2) ++ ", " ++ show ((seed + 2) * 3) ++ "))"

  compileAndRunGMP dir "ownedExactTuples" program [expectedReturn, expectedOutput]

-- | Exercise borrowed exact-field ADT inputs and independently owned outputs
-- and returns, including exact fields nested through another ADT and a tuple.
ownedExactADTs :: Assertion
ownedExactADTs = withSystemTempDirectory "sbv-owned-exact-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen SExactAggregate
        let leaf                      = getExactAggregate_1 source
            values                    = getExactAggregate_2 source
            integerValue              = getExactLeaf_1 leaf
            realValue                 = getExactLeaf_2 leaf
            (tupleInteger, tupleReal) = untuple values
            outputValues              = tuple (tupleInteger + 2, tupleReal + 3)
            outputLeaf                = sExactLeaf (integerValue + 1) (realValue / 7)
            outputAggregate           = sExactAggregate outputLeaf outputValues
            resultValues              = tuple (tupleInteger * 3, tupleReal / 5)
            resultLeaf                = sExactLeaf (integerValue * 2) (realValue + 1)
            resultAggregate           = sExactAggregate resultLeaf resultValues
        cgOutput "output" outputAggregate
        cgOutput "sameAsResult" (source .== resultAggregate)
        cgReturn resultAggregate
      seed           = 2 ^ (130 :: Int) + 1
      expectedOutput = "output =ExactAggregate(ExactLeaf(" ++ show (seed + 1)
                    ++ ", " ++ show (seed + 1) ++ "/7), (" ++ show (seed + 3)
                    ++ ", " ++ show (seed + 5) ++ "))"
      expectedReturn = "ExactAggregate(ExactLeaf(" ++ show (seed * 2)
                    ++ ", " ++ show (seed + 2) ++ "), (" ++ show (3 * (seed + 1))
                    ++ ", " ++ show (seed + 2) ++ "/5))"

  compileAndRunGMP dir "ownedExactADTs" program [expectedReturn, expectedOutput, "sameAsResult = 0"]

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
      tupleProgram increment = do
        cgOverwriteFiles True
        cgSetDriverValues [tupleSeed]
        source <- cgInput "source" :: SBVCodeGen (SBV (Integer, AlgReal))
        let (integerValue, realValue) = untuple source
        cgReturn (tuple (integerValue + fromInteger increment, realValue + fromInteger increment))
      adtProgram increment = do
        cgOverwriteFiles True
        cgSetDriverValues [adtSeed]
        source <- cgInput "source" :: SBVCodeGen SExactAggregate
        let leaf                      = getExactAggregate_1 source
            integerValue              = getExactLeaf_1 leaf
            realValue                 = getExactLeaf_2 leaf
            (tupleInteger, tupleReal) = untuple (getExactAggregate_2 source)
            integerAmount             = fromInteger increment :: SInteger
            realAmount                = fromInteger increment :: SReal
            resultLeaf                = sExactLeaf (integerValue + integerAmount) (realValue + realAmount)
            resultValues              = tuple (tupleInteger + integerAmount, tupleReal + realAmount)
        cgReturn (sExactAggregate resultLeaf resultValues)
      wideSample = negate (2 ^ (670 :: Int)) + 12345
      tupleSeed  = 2 ^ (140 :: Int)
      adtSeed    = 2 ^ (150 :: Int) + 1

  (_, cfg, bundle) <- compileToCLib' "exactNumberLibrary"
    [ ("integerPart", integerProgram)
    , ("realPart", realProgram)
    , ("widePart", wideProgram)
    , ("incrementTuple", tupleProgram 1)
    , ("addTwoTuple", tupleProgram 2)
    , ("incrementADT", adtProgram 1)
    , ("addTwoADT", adtProgram 2)
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
  assertOutput stdoutText ("(" ++ show (tupleSeed + 1) ++ ", " ++ show (tupleSeed + 2) ++ ")")
  assertOutput stdoutText ("(" ++ show (tupleSeed + 2) ++ ", " ++ show (tupleSeed + 3) ++ ")")
  assertOutput stdoutText ("ExactAggregate(ExactLeaf(" ++ show (adtSeed + 1) ++ ", " ++ show (adtSeed + 2)
                         ++ "), (" ++ show (adtSeed + 2) ++ ", " ++ show (adtSeed + 3) ++ "))")
  assertOutput stdoutText ("ExactAggregate(ExactLeaf(" ++ show (adtSeed + 2) ++ ", " ++ show (adtSeed + 3)
                         ++ "), (" ++ show (adtSeed + 3) ++ ", " ++ show (adtSeed + 4) ++ "))")

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
