-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.ArbitraryFloats
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compile-and-run tests for LibBF-backed arbitrary floating-point C lowering.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.ArbitraryFloats (tests) where

import Control.Exception         (IOException, catch)
import Data.List                 (isInfixOf, isPrefixOf, isSuffixOf)
import Numeric                   (showHex)
import System.Directory          (doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit               (ExitCode(..))
import System.FilePath           ((</>), takeDirectory)
import System.IO.Temp            (withSystemTempDirectory)
import System.Process            (readProcessWithExitCode)
import Test.Tasty.HUnit          (assertBool, assertEqual)

import Data.SBV.Internals

import Utils.SBVTestFramework hiding ((#))

-- | Arbitrary floating-point C backend tests.
tests :: TestTree
tests = testGroup "CodeGeneration.ArbitraryFloats"
  [ testCase "compile and execute arithmetic" arbitraryFloatArithmetic
  , testCase "compile and execute a nonstandard wide format" arbitraryFloatWideFormat
  , testCase "compile and execute classification" arbitraryFloatClassification
  , testCase "compile and execute rounding modes" arbitraryFloatRoundingModes
  , testCase "compile and execute symbolic rounding modes" arbitraryFloatSymbolicRoundingMode
  , testCase "compile and execute native rounding modes" nativeFloatRoundingModes
  , testCase "compile and execute special arithmetic" arbitraryFloatSpecialArithmetic
  , testCase "compile and execute arbitrary-float table lookup" arbitraryFloatTableLookup
  , testCase "preserve arbitrary floating-point array-key equality" arbitraryFloatArrayKeys
  , testCase "compile and execute an arbitrary-float callback-backed array" arbitraryFloatArrayInput
  , testCase "compile and execute an arbitrary-float structured lambda array" arbitraryFloatLambdaArray
  , testCase "compile and execute a mixed repeated-type library" mixedRepeatedTypeLibrary
  , testCase "compile a repeated-type library without a driver" repeatedTypeLibraryWithoutDriver
  ]

-- | Exercise LibBF-backed quadruple arithmetic and floating-point predicates.
arbitraryFloatArithmetic :: Assertion
arbitraryFloatArithmetic = withSystemTempDirectory "sbv-arbitrary-float" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 2, -17]
        a <- cgInput "a" :: SBVCodeGen SFPQuad
        b <- cgInput "b" :: SBVCodeGen SFPQuad
        c <- cgInput "c" :: SBVCodeGen SInt64
        let added     = fpAdd sRNE a b
            fused     = fpFMA sRNE a b b
            half      = toSFloatingPoint sRNE fused :: SFPHalf
            viaHalf   = toSFloatingPoint sRNE half :: SFPQuad
            asDouble  = fromSFloatingPoint sRNE fused :: SDouble
            viaDouble = toSFloatingPoint sRNE asDouble :: SFPQuad
            fromInt   = toSFloatingPoint sRNE c :: SFPQuad
            backInt   = fromSFloatingPoint sRNE fromInt :: SInt64
            bits      = sFloatingPointAsSWord viaDouble :: SWord 128
            roundTrip = sWordAsSFloatingPoint bits :: SFPQuad
        cgOutput "added" added
        cgOutput "fusedBits" bits
        cgReturn $ ite (fpIsNormal a .&& a .> b .&& fpIsEqualObject fused viaHalf .&& fpIsEqualObject fused roundTrip .&& backInt .== c) roundTrip added
      bias     = 2 ^ (14 :: Int) - 1 :: Integer
      eightRaw = (bias + 3) * 2 ^ (112 :: Int)
  compileAndRunLibBF dir "arbitraryFloatArithmetic" program (asHex 2 eightRaw)

-- | Exercise a nonstandard format whose interchange value spans four limbs.
arbitraryFloatWideFormat :: Assertion
arbitraryFloatWideFormat = withSystemTempDirectory "sbv-arbitrary-float-wide-format" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 5]
        a <- cgInput "a" :: SBVCodeGen (SFloatingPoint 17 237)
        b <- cgInput "b" :: SBVCodeGen (SFloatingPoint 17 237)
        let result = fpAdd sRNE a b
            bits   = sFloatingPointAsSWord result :: SWord 254
        cgOutput "bits" bits
        cgReturn result
      bias     = 2 ^ (16 :: Int) - 1 :: Integer
      eightRaw = (bias + 3) * 2 ^ (236 :: Int)
  compileAndRunLibBF dir "arbitraryFloatWideFormat" program (asHex 4 eightRaw)

-- | Exercise special-value classification through raw half-precision inputs.
arbitraryFloatClassification :: Assertion
arbitraryFloatClassification = withSystemTempDirectory "sbv-arbitrary-float-classification" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0x7e00, 0x8000, 0x0001, 0x7c00]
        nanBits <- cgInput "nanBits"          :: SBVCodeGen (SWord 16)
        nzBits  <- cgInput "negativeZeroBits" :: SBVCodeGen (SWord 16)
        subBits <- cgInput "subnormalBits"    :: SBVCodeGen (SWord 16)
        infBits <- cgInput "infinityBits"     :: SBVCodeGen (SWord 16)
        let nanValue     = sWordAsSFloatingPoint nanBits :: SFPHalf
            negativeZero = sWordAsSFloatingPoint nzBits :: SFPHalf
            subnormal    = sWordAsSFloatingPoint subBits :: SFPHalf
            infValue     = sWordAsSFloatingPoint infBits :: SFPHalf
            positiveZero = 0 :: SFPHalf
        cgReturn $ pack [fpIsNaN nanValue
                        , nanValue ./= nanValue
                        , fpIsEqualObject nanValue nanValue
                        , fpIsZero negativeZero
                        , fpIsNegative negativeZero
                        , sNot (fpIsEqualObject negativeZero positiveZero)
                        , negativeZero .== positiveZero
                        , fpIsSubnormal subnormal
                        , fpIsPositive subnormal
                        , sNot (fpIsNormal subnormal)
                        , fpIsInfinite infValue
                        , sNot (fpIsNormal infValue)]
  compileAndRunLibBF dir "arbitraryFloatClassification" program "0x0fff"
 where pack :: [SBool] -> SWord16
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048])

-- | Exercise all IEEE rounding modes on an exactly halfway format conversion.
arbitraryFloatRoundingModes :: Assertion
arbitraryFloatRoundingModes = withSystemTempDirectory "sbv-arbitrary-float-rounding" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2049, 2048]
        numValue <- cgInput "numerator"   :: SBVCodeGen SFPQuad
        denValue <- cgInput "denominator" :: SBVCodeGen SFPQuad
        let value = fpDiv sRNE numValue denValue
            rne   = rawHalf (toSFloatingPoint sRNE value)
            rna   = rawHalf (toSFloatingPoint sRNA value)
            rtp   = rawHalf (toSFloatingPoint sRTP value)
            rtn   = rawHalf (toSFloatingPoint sRTN value)
            rtz   = rawHalf (toSFloatingPoint sRTZ value)
        cgReturn (rne # rna # rtp # rtn # rtz :: SWord 80)
      expected = foldl (\acc word -> acc * 2 ^ (16 :: Int) + word) 0 [0x3c00, 0x3c01, 0x3c01, 0x3c00, 0x3c00]
  compileAndRunLibBF dir "arbitraryFloatRoundingModes" program (asHex 2 expected)
 where rawHalf :: SFPHalf -> SWord 16
       rawHalf = sFloatingPointAsSWord

-- | Exercise a runtime-selected rounding mode in arithmetic and conversion.
arbitraryFloatSymbolicRoundingMode :: Assertion
arbitraryFloatSymbolicRoundingMode = withSystemTempDirectory "sbv-arbitrary-float-symbolic-rounding" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 0, 1, 2, 3, 4, 2049, 2048, 1, 3]
        choose    <- cgInput "chooseInputMode" :: SBVCodeGen SBool
        modeRNE   <- cgInput "rne"             :: SBVCodeGen SRoundingMode
        modeRNA   <- cgInput "rna"             :: SBVCodeGen SRoundingMode
        modeRTP   <- cgInput "rtp"             :: SBVCodeGen SRoundingMode
        modeRTN   <- cgInput "rtn"             :: SBVCodeGen SRoundingMode
        modeRTZ   <- cgInput "rtz"             :: SBVCodeGen SRoundingMode
        numValue  <- cgInput "numerator"       :: SBVCodeGen SFPQuad
        denValue  <- cgInput "denominator"     :: SBVCodeGen SFPQuad
        one       <- cgInput "one"             :: SBVCodeGen SFPHalf
        three     <- cgInput "three"           :: SBVCodeGen SFPHalf
        let runtimeMode mode = ite choose mode sRTZ
            value            = fpDiv sRNE numValue denValue
            rne              = rawHalf (toSFloatingPoint (runtimeMode modeRNE) value)
            rna              = rawHalf (toSFloatingPoint (runtimeMode modeRNA) value)
            rtp              = rawHalf (toSFloatingPoint (runtimeMode modeRTP) value)
            rtn              = rawHalf (toSFloatingPoint (runtimeMode modeRTN) value)
            rtz              = rawHalf (toSFloatingPoint (runtimeMode modeRTZ) value)
            divided          = rawHalf (fpDiv (runtimeMode modeRTP) one three)
        cgOutput "selectedMode" (runtimeMode modeRTP)
        cgReturn (rne # rna # rtp # rtn # rtz # divided :: SWord 96)
      expected = foldl (\acc word -> acc * 2 ^ (16 :: Int) + word) 0 [0x3c00, 0x3c01, 0x3c01, 0x3c00, 0x3c00, 0x3556]
  compileAndRunLibBF dir "arbitraryFloatSymbolicRoundingMode" program (asHex 2 expected)
 where rawHalf :: SFPHalf -> SWord 16
       rawHalf = sFloatingPointAsSWord

-- | Exercise all constant rounding modes and runtime-selected modes while
-- retaining native @float@ and @double@ values at the generated C boundary.
nativeFloatRoundingModes :: Assertion
nativeFloatRoundingModes = withSystemTempDirectory "sbv-native-float-rounding" $ \dir -> do
  let floatProgram = do
        cgOverwriteFiles True
        cgSetDriverValues [0x3f800000, 0x33800000, 1, 2]
        oneRaw   <- cgInput "oneBits"  :: SBVCodeGen SWord32
        halfBits <- cgInput "halfBits" :: SBVCodeGen SWord32
        modeRNA  <- cgInput "modeRNA"  :: SBVCodeGen SRoundingMode
        modeRTP  <- cgInput "modeRTP"  :: SBVCodeGen SRoundingMode
        let one     = sWord32AsSFloat oneRaw
            halfUlp = sWord32AsSFloat halfBits
            raw mode = sFromIntegral (sFloatAsSWord32 (fpAdd mode one halfUlp)) :: SWord 32
        cgReturn (raw sRNE # raw sRNA # raw sRTP # raw sRTN # raw sRTZ # raw modeRNA # raw modeRTP :: SWord 224)

      doubleProgram = do
        cgOverwriteFiles True
        cgSetDriverValues [0x3ff0000000000000, 0x3ca0000000000000, 1, 2]
        oneRaw   <- cgInput "oneBits"  :: SBVCodeGen SWord64
        halfBits <- cgInput "halfBits" :: SBVCodeGen SWord64
        modeRNA  <- cgInput "modeRNA"  :: SBVCodeGen SRoundingMode
        modeRTP  <- cgInput "modeRTP"  :: SBVCodeGen SRoundingMode
        let one     = sWord64AsSDouble oneRaw
            halfUlp = sWord64AsSDouble halfBits
            raw mode = sFromIntegral (sDoubleAsSWord64 (fpAdd mode one halfUlp)) :: SWord 64
        cgReturn (raw sRNE # raw sRNA # raw sRTP # raw sRTN # raw sRTZ # raw modeRNA # raw modeRTP :: SWord 448)

      scalarProgram = do
        cgOverwriteFiles True
        cgSetDriverValues [0x3f800000, 0x33800000]
        oneRaw   <- cgInput "oneBits"  :: SBVCodeGen SWord32
        halfBits <- cgInput "halfBits" :: SBVCodeGen SWord32
        let result = fpAdd sRNA (sWord32AsSFloat oneRaw) (sWord32AsSFloat halfBits)
        cgOutput "resultBits" (sFloatAsSWord32 result)
        cgReturn result

      floatOne      = 0x3f800000
      floatNext     = 0x3f800001
      doubleOne     = 0x3ff0000000000000
      doubleNext    = 0x3ff0000000000001
      assemble width = foldl (\acc word -> acc * 2 ^ width + word) 0
      floatExpected  = assemble (32 :: Int) [floatOne, floatNext, floatNext, floatOne, floatOne, floatNext, floatNext]
      doubleExpected = assemble (64 :: Int) [doubleOne, doubleNext, doubleNext, doubleOne, doubleOne, doubleNext, doubleNext]

  compileAndRunLibBF dir "nativeFloatRoundingModesFloat" floatProgram (asHex 4 floatExpected)
  compileAndRunLibBF dir "nativeFloatRoundingModesDouble" doubleProgram (asHex 7 doubleExpected)
  compileAndRunLibBF dir "nativeFloatRoundingScalar" scalarProgram "resultBits = 0x3f800001UL"

-- | Exercise LibBF encoding of subnormal results, NaN, and signed zero.
arbitraryFloatSpecialArithmetic :: Assertion
arbitraryFloatSpecialArithmetic = withSystemTempDirectory "sbv-arbitrary-float-special" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0x0001, 0x7c00, 0x8000, 5, 2]
        subBits <- cgInput "subnormalBits"    :: SBVCodeGen (SWord 16)
        infBits <- cgInput "infinityBits"     :: SBVCodeGen (SWord 16)
        nzBits  <- cgInput "negativeZeroBits" :: SBVCodeGen (SWord 16)
        five    <- cgInput "five"             :: SBVCodeGen SFPHalf
        two     <- cgInput "two"              :: SBVCodeGen SFPHalf
        let subnormal    = sWordAsSFloatingPoint subBits :: SFPHalf
            infValue     = sWordAsSFloatingPoint infBits :: SFPHalf
            negativeZero = sWordAsSFloatingPoint nzBits :: SFPHalf
            doubled      = rawHalf (fpAdd sRNE subnormal subnormal)
            nanResult    = rawHalf (fpSub sRNE infValue infValue)
            zeroResult   = rawHalf (fpSqrt sRNE negativeZero)
            remResult    = rawHalf (fpRem five two)
            roundResult  = rawHalf (fpRoundToIntegral sRNE (fpDiv sRNE five two))
            minResult    = rawHalf (fpMin five two)
            maxResult    = rawHalf (fpMax five two)
            absResult    = rawHalf (abs (negate five))
        cgReturn (doubled # nanResult # zeroResult # remResult # roundResult # minResult # maxResult # absResult :: SWord 128)
      expected = foldl (\acc word -> acc * 2 ^ (16 :: Int) + word) 0 [0x0002, 0x7e00, 0x8000, 0x3c00, 0x4000, 0x4000, 0x4500, 0x4500]
  compileAndRunLibBF dir "arbitraryFloatSpecialArithmetic" program (asHex 2 expected)
 where rawHalf :: SFPHalf -> SWord 16
       rawHalf = sFloatingPointAsSWord

-- | Exercise a finite table containing computed arbitrary-precision floating
-- point values. The table is emitted after the computation on which it
-- depends and its result remains an ordinary by-value interchange object.
arbitraryFloatTableLookup :: Assertion
arbitraryFloatTableLookup = withSystemTempDirectory "sbv-arbitrary-float-table" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgPerformRTCs True
        cgSetDriverValues [1, 3]
        index <- cgInput "index" :: SBVCodeGen SWord8
        value <- cgInput "value" :: SBVCodeGen SFPQuad
        let selected = select [value, fpAdd sRNE value 2] 99 index
        cgReturn (sFloatingPointAsSWord selected :: SWord 128)
      bias    = 2 ^ (14 :: Int) - 1 :: Integer
      fiveRaw = (bias + 2) * 2 ^ (112 :: Int) + 2 ^ (110 :: Int)
  compileAndRunLibBF dir "arbitraryFloatTableLookup" program (asHex 2 fiveRaw)

-- | Check that LibBF-backed array keys use SMT object equality: NaNs match,
-- while positive and negative zero remain distinct.
arbitraryFloatArrayKeys :: Assertion
arbitraryFloatArrayKeys = withSystemTempDirectory "sbv-arbitrary-float-array-keys" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0x7e00, 0x0000, 0x8000]
        nanBits      <- cgInput "nanBits"      :: SBVCodeGen (SWord 16)
        positiveBits <- cgInput "positiveBits" :: SBVCodeGen (SWord 16)
        negativeBits <- cgInput "negativeBits" :: SBVCodeGen (SWord 16)
        let nanKey       = sWordAsSFloatingPoint nanBits :: SFPHalf
            positiveZero = sWordAsSFloatingPoint positiveBits :: SFPHalf
            negativeZero = sWordAsSFloatingPoint negativeBits :: SFPHalf
            base         = constArray 3
            withNaN      = writeArray base nanKey 11
            withZero     = writeArray withNaN positiveZero 12
            flags        = [ readArray withZero nanKey .== (11 :: SWord8)
                           , readArray withZero positiveZero .== (12 :: SWord8)
                           , readArray withZero negativeZero .== (3 :: SWord8)
                           ]
        cgReturn (sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4]) :: SWord8)
  compileAndRunLibBF dir "arbitraryFloatArrayKeys" program "= 7"

-- | Exercise a callback-backed array whose returned values use LibBF's raw
-- arbitrary floating-point interchange representation.
arbitraryFloatArrayInput :: Assertion
arbitraryFloatArrayInput = withSystemTempDirectory "sbv-arbitrary-float-array-input" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 7]
        source <- cgInput "source" :: SBVCodeGen (SArray Word8 (FloatingPoint 15 113))
        key    <- cgInput "key"    :: SBVCodeGen SWord8
        cgReturn (sFloatingPointAsSWord (readArray source key) :: SWord 128)
      bias     = 2 ^ (14 :: Int) - 1 :: Integer
      threeRaw = (bias + 1) * 2 ^ (112 :: Int) + 2 ^ (111 :: Int)
  compileAndRunLibBF dir "arbitraryFloatArrayInput" program (asHex 2 threeRaw)

-- | Exercise a LibBF conversion that occurs only inside a retained array
-- lambda, ensuring its format-specific runtime helper is still discovered.
arbitraryFloatLambdaArray :: Assertion
arbitraryFloatLambdaArray = withSystemTempDirectory "sbv-arbitrary-float-lambda-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3]
        key <- cgInput "key" :: SBVCodeGen SWord8
        let source = lambdaArray (\index -> toSFloatingPoint sRNE index :: SFloatingPoint 15 113)
                     :: SArray Word8 (FloatingPoint 15 113)
        cgReturn (sFloatingPointAsSWord (readArray source key) :: SWord 128)
      bias     = 2 ^ (14 :: Int) - 1 :: Integer
      threeRaw = (bias + 1) * 2 ^ (112 :: Int) + 2 ^ (111 :: Int)
  compileAndRunLibBF dir "arbitraryFloatLambdaArray" program (asHex 2 threeRaw)

-- | Exercise repeated declarations and dependencies in a mixed generated library.
mixedRepeatedTypeLibrary :: Assertion
mixedRepeatedTypeLibrary = withSystemTempDirectory "sbv-mixed-repeated-library" $ \dir -> do
  let configure values = do
        cgOverwriteFiles True
        cgSetDriverValues values

      wideAddProgram = do
        configure [5]
        value <- cgInput "value" :: SBVCodeGen (SWord 673)
        cgReturn (value + 1)

      wideXorProgram = do
        configure [7]
        value <- cgInput "value" :: SBVCodeGen (SWord 673)
        cgReturn (value `xor` 3)

      fpDivideProgram = do
        configure [2, 1, 3]
        mode  <- cgInput "mode"  :: SBVCodeGen SRoundingMode
        value <- cgInput "value" :: SBVCodeGen SFPHalf
        three <- cgInput "three" :: SBVCodeGen SFPHalf
        cgReturn (fpDiv mode value three)

      fpDivideAgainProgram = do
        configure [3, 1, 3]
        mode  <- cgInput "mode"  :: SBVCodeGen SRoundingMode
        value <- cgInput "value" :: SBVCodeGen SFPHalf
        three <- cgInput "three" :: SBVCodeGen SFPHalf
        cgReturn (fpDiv mode value three)

      integerAddProgram = do
        configure [2 ^ (130 :: Int)]
        value <- cgInput "value" :: SBVCodeGen SInteger
        cgReturn (value + 7)

      integerMulProgram = do
        configure [9]
        value <- cgInput "value" :: SBVCodeGen SInteger
        cgReturn (value * 3)

      realDivideProgram = do
        configure [5]
        value <- cgInput "value" :: SBVCodeGen SReal
        cgReturn (value / 3)

      realAddProgram = do
        configure [2]
        value <- cgInput "value" :: SBVCodeGen SReal
        cgReturn (value + 1 / 7)

      components = [ ("wideAdd",       wideAddProgram)
                   , ("wideXor",       wideXorProgram)
                   , ("fpDivide",      fpDivideProgram)
                   , ("fpDivideAgain", fpDivideAgainProgram)
                   , ("integerAdd",    integerAddProgram)
                   , ("integerMul",    integerMulProgram)
                   , ("realDivide",    realDivideProgram)
                   , ("realAdd",       realAddProgram)
                   ]

  (includeDir, archive) <- locateLibBF
  (_, cfg, bundle) <- compileToCLib' "mixedRepeatedTypeLibrary" components
  renderCgPgmBundle (Just dir) (cfg, bundle)
  writeFile (dir </> "libbf.mk") $ unlines
    [ "CCFLAGS=-std=c11 -Wall -Werror -I" ++ includeDir ++ " ${GMP_CFLAGS}"
    , "LDFLAGS=" ++ archive ++ " -lm ${GMP_LIBS}"
    ]

  (makeExit, _, makeError) <- readProcessWithExitCode "make" ["-C", dir] ""
  assertEqual makeError ExitSuccess makeExit

  let driverExecutable = dir </> "mixedRepeatedTypeLibrary_driver"
  (runExit, stdoutText, runError) <- readProcessWithExitCode driverExecutable [] ""
  assertEqual runError ExitSuccess runExit
  mapM_ (assertOutput stdoutText)
    [ asHex 11 6
    , asHex 11 4
    , "0x0000000000003556"
    , "0x0000000000003555"
    , show (2 ^ (130 :: Int) + 7 :: Integer)
    , "27"
    , "5/3"
    , "15/7"
    ]

  makefile <- readFile (dir </> "Makefile")
  assertBool "Mixed library Makefile lost the LibBF dependency" ("-lbf" `isInfixOf` makefile)
  assertBool "Mixed library Makefile lost the GMP dependency" ("${GMP_LIBS}" `isInfixOf` makefile)
 where assertOutput stdoutText fragment =
         assertBool ("Expected generated library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText)

-- | Exercise archive-only generation with a type shared across translation units.
repeatedTypeLibraryWithoutDriver :: Assertion
repeatedTypeLibraryWithoutDriver = withSystemTempDirectory "sbv-repeated-library-no-driver" $ \dir -> do
  let component operation = do
        cgOverwriteFiles True
        cgGenerateDriver False
        value <- cgInput "value" :: SBVCodeGen (SWord 673)
        cgReturn (operation value)
      components = [ ("increment", component (+ 1))
                   , ("decrement", component (subtract 1))
                   ]

  (_, cfg, bundle) <- compileToCLib' "repeatedTypeLibraryWithoutDriver" components
  renderCgPgmBundle (Just dir) (cfg, bundle)

  (makeExit, _, makeError) <- readProcessWithExitCode "make" ["-C", dir] ""
  assertEqual makeError ExitSuccess makeExit
  archiveExists <- doesFileExist (dir </> "repeatedTypeLibraryWithoutDriver.a")
  driverExists  <- doesFileExist (dir </> "repeatedTypeLibraryWithoutDriver_driver.c")
  assertBool "Generated library archive is missing" archiveExists
  assertBool "Driver generation was disabled, but a driver was emitted" (not driverExists)

-- | Generate and execute a C program linked to the LibBF bundled with the
-- Haskell @libBF@ package.
compileAndRunLibBF :: FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRunLibBF dir functionName program expected = do
  (includeDir, archive) <- locateLibBF
  compileAndRunWith ["-I" ++ includeDir, archive, "-lm"] dir functionName program expected

-- | Generate, compile, and execute C with additional compiler/linker options.
compileAndRunWith :: [String] -> FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRunWith ccOptions dir functionName program expected = do
  (_, cfg, bundle) <- compileToC' functionName program
  renderCgPgmBundle (Just dir) (cfg, bundle)

  let source = dir </> functionName ++ ".c"
      driver = dir </> functionName ++ "_driver.c"
      exe    = dir </> functionName ++ "_driver"
  (ccExit, _, ccErr) <- readProcessWithExitCode "cc" (["-std=c11", "-Wall", "-Werror", source, driver, "-o", exe] ++ ccOptions) ""
  assertEqual ccErr ExitSuccess ccExit

  (runExit, out, runErr) <- readProcessWithExitCode exe [] ""
  assertEqual runErr ExitSuccess runExit
  assertBool ("Expected generated output to contain " ++ expected ++ ", received:\n" ++ out) (expected `isInfixOf` out)

-- | Locate the header and static archive installed for the Haskell @libBF@
-- dependency so integration tests exercise the same C implementation.
locateLibBF :: IO (FilePath, FilePath)
locateLibBF = do
  (_, pathOutput, pathError) <- readProcessWithExitCode "cabal" ["path"] ""
  let storePrefix = "compiler-store-path: "
      stores      = [drop (length storePrefix) line | line <- lines pathOutput, storePrefix `isInfixOf` line]
  store <- case stores of
             path:_ -> pure path
             []     -> fail $ "Unable to find Cabal store: " ++ pathError
  packages <- listDirectory store
  let libBFDirs = [store </> entry | entry <- packages, "lbBF-" `isPrefixOf` entry]
  header  <- firstSuccessful [findInstalledFile path "libbf.h" | path <- libBFDirs]
  archive <- firstSuccessful [findInstalledFile path "libHSlbBF" | path <- libBFDirs]
  pure (takeDirectory header, archive)

-- | Recursively find an installed file by exact name or filename prefix.
findInstalledFile :: FilePath -> String -> IO FilePath
findInstalledFile root sought = do
  entries <- listDirectory root
  search entries
 where search []           = fail $ "Unable to find " ++ sought ++ " below " ++ root
       search (entry:rest) = do
         let path = root </> entry
         isDir  <- doesDirectoryExist path
         isFile <- doesFileExist path
         if isFile && matches entry
           then pure path
           else if isDir
                  then findInstalledFile path sought `catchIO` search rest
                  else search rest

       matches entry
         | sought == "libHSlbBF" = sought `isPrefixOf` entry && ".a" `isSuffixOf` entry
         | True                  = entry == sought

-- | Return the first successful filesystem search result.
firstSuccessful :: [IO a] -> IO a
firstSuccessful = foldr catchIO (fail "Unable to locate the installed libBF package")

-- | Recover from an expected filesystem-search failure with another search.
catchIO :: IO a -> IO a -> IO a
catchIO action fallback = action `catch` \(_ :: IOException) -> fallback

-- | Render the fixed-limb hexadecimal form printed by generated drivers.
asHex :: Int -> Integer -> String
asHex limbCount value = "0x" ++ replicate (16 * limbCount - length h) '0' ++ h
 where h = showHex value ""
