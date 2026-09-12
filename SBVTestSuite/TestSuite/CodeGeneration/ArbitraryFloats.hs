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

import Control.Exception         (ErrorCall, IOException, catch, displayException, try)
import Data.List                 (isInfixOf, isPrefixOf, isSuffixOf)
import Numeric                   (showHex)
import System.Directory          (doesDirectoryExist, doesFileExist, listDirectory)
import System.Environment        (lookupEnv)
import System.Exit               (ExitCode(..))
import System.FilePath           ((</>), takeDirectory)
import System.IO.Temp            (withSystemTempDirectory)
import System.Process            (readProcessWithExitCode)
import Test.Tasty.HUnit          (assertBool, assertEqual)

import qualified Data.SBV.Dynamic as D

import Data.SBV.Internals
import Data.SBV.Tuple (tuple, untuple)

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
  , testCase "convert between native floats and bit-vectors" nativeFloatBitVectorConversions
  , testCase "convert native floats across non-native widths" nativeFloatWidthConversions
  , testCase "preserve native floating casts under caller rounding modes" nativeFloatCastEnvironment
  , testCase "totalize exceptional native floating casts without C overflow" nativeFloatExceptionalCasts
  , testCase "keep exact native floating casts free of LibBF" nativeExactFloatConversions
  , testCase "convert between native floats and exact numbers" nativeFloatExactConversions
  , testCase "convert mapped integers with explicit float rounding" mappedIntegerFloatConversions
  , testCase "convert mapped reals across numeric representations" mappedRealConversions
  , testCase "reject unsupported long-double numeric bridges before rendering" longDoubleNumericBoundaries
  , testCase "compile and execute special arithmetic" arbitraryFloatSpecialArithmetic
  , testCase "compile and execute arbitrary-float table lookup" arbitraryFloatTableLookup
  , testCase "preserve arbitrary floating-point array-key equality" arbitraryFloatArrayKeys
  , testCase "compile and execute an arbitrary-float callback-backed array" arbitraryFloatArrayInput
  , testCase "compile and execute an arbitrary-float structured lambda array" arbitraryFloatLambdaArray
  , testCase "compile and execute an arbitrary-float structured lambda table" arbitraryFloatLambdaTable
  , testCase "convert between arbitrary floats and exact numbers" arbitraryFloatExactConversions
  , testCase "compile and execute a mixed repeated-type library" mixedRepeatedTypeLibrary
  , testCase "compile a repeated-type library without a driver" repeatedTypeLibraryWithoutDriver
  , testCase "compile a wide arbitrary-float tuple" wideFloatingTuple
  , testCase "preserve dependencies with optional library files" optionalLibraryFiles
  ]

-- | Keep LibBF requirements when its component disables Makefile generation,
-- and associate an enabled driver with its own component after a disabled one.
optionalLibraryFiles :: Assertion
optionalLibraryFiles = mapM_ check [False, True]
 where check generateMakefile = withSystemTempDirectory "sbv-optional-library-files" $ \dir -> do
         (includeDir, archive) <- locateLibBF
         (_, cfg, bundle) <- compileToCLib' "optionalLibrary"
           [ ("scalar", do
                 cgOverwriteFiles True
                 cgGenerateDriver False
                 cgGenerateMakefile generateMakefile
                 value <- cgInput "value" :: SBVCodeGen SWord8
                 cgReturn (value + 1))
           , ("half", do
                 cgOverwriteFiles True
                 cgGenerateMakefile False
                 cgSetDriverValues [1]
                 value <- cgInput "value" :: SBVCodeGen SFPHalf
                 cgReturn (value + 1))
           ]
         renderCgPgmBundle (Just dir) (cfg, bundle)
         hasMakefile <- doesFileExist (dir </> "Makefile")
         assertEqual "Unexpected optional Makefile" generateMakefile hasMakefile
         if generateMakefile
           then do makefile <- readFile (dir </> "Makefile")
                   assertBool "Hidden component lost its LibBF link dependency" ("-lbf" `isInfixOf` makefile)
           else pure ()
         let driverPath = dir </> "driver"
         (buildExit, _, buildError) <- readProcessWithExitCode "cc"
           [ "-std=c11", "-Wall", "-Werror", "-I" ++ includeDir
           , dir </> "scalar.c", dir </> "half.c", dir </> "optionalLibrary_driver.c"
           , archive, "-lm", "-o", driverPath
           ] ""
         assertEqual buildError ExitSuccess buildExit
         (runExit, outputText, runError) <- readProcessWithExitCode driverPath [] ""
         assertEqual runError ExitSuccess runExit
         assertBool outputText ("Driver run for half:" `isInfixOf` outputText && asHex 1 0x4000 `isInfixOf` outputText)

-- | Exercise tuple fields whose value representations are generated wide
-- bit-vector and arbitrary floating-point structures.
wideFloatingTuple :: Assertion
wideFloatingTuple = withSystemTempDirectory "sbv-wide-floating-tuple" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5]
        source <- cgInput "source" :: SBVCodeGen (SBV (WordN 65, FloatingPoint 7 19))
        let (word, float) = untuple source
        cgReturn (tuple (word + 1, float + 1))

  compileAndRunLibBF dir "wideFloatingTuple" program "(0x00000000000000000000000000000006, 0x"

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
                        , sNot (fpIsNormal infValue)
                        , distinct [nanValue, nanValue, positiveZero]
                        , sNot (distinct [negativeZero, positiveZero])]
  compileAndRunLibBF dir "arbitraryFloatClassification" program "0x3fff"
 where pack :: [SBool] -> SWord16
       pack flags = sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192])

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

-- | Exercise all rounding directions between native floats and exact-width
-- bit-vectors.
nativeFloatBitVectorConversions :: Assertion
nativeFloatBitVectorConversions = withSystemTempDirectory "sbv-native-float-bit-vector" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [16777217, 5, 2]
        nativeInteger <- cgInput "nativeInteger" :: SBVCodeGen SInt32
        five          <- cgInput "five"          :: SBVCodeGen SFloat
        two           <- cgInput "two"           :: SBVCodeGen SFloat
        let nativeRNE   = toSFloat sRNE nativeInteger
            nativeRTP   = toSFloat sRTP nativeInteger
            twoAndAHalf = fpDiv sRNE five two
            nativeEven  = fromSFloat sRNE twoAndAHalf :: SInt32
            nativeAway  = fromSFloat sRNA twoAndAHalf :: SInt32
            nativeDown  = fromSFloat sRTN twoAndAHalf :: SInt32
            nativeUp    = fromSFloat sRTP twoAndAHalf :: SInt32
        cgReturn $ nativeRNE .== 16777216
               .&& nativeRTP .== 16777218
               .&& nativeEven .== 2
               .&& nativeAway .== 3
               .&& nativeDown .== 2
               .&& nativeUp   .== 3
  compileAndRunLibBF dir "nativeFloatBitVectorConversions" program "= 1"

-- | Exercise explicitly rounded native float-to-float conversion, RNE
-- conversion to and from a limb-backed bit-vector, and the one-bit scalar
-- fallback type.
nativeFloatWidthConversions :: Assertion
nativeFloatWidthConversions = withSystemTempDirectory "sbv-native-float-width-conversions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [halfwayBits, 42, 1, 1]
        rawHalfway <- cgInput "rawHalfway" :: SBVCodeGen SWord64
        wideValue  <- svCgInput wideKind "wideValue"
        oneBit     <- svCgInput oneBitKind "oneBit"
        runtimeRNA <- cgInput "runtimeRNA" :: SBVCodeGen SRoundingMode
        let halfway      = sWord64AsSDouble rawHalfway
            floatBits rm = sFloatAsSWord32 (toSFloat rm halfway)
            nativeChecks = floatBits sRNE       .== floatOne
                       .&& floatBits sRNA       .== floatNext
                       .&& floatBits sRTP       .== floatNext
                       .&& floatBits sRTN       .== floatOne
                       .&& floatBits sRTZ       .== floatOne
                       .&& floatBits runtimeRNA .== floatNext
            wideAsDouble = D.svCastToFP KDouble rneValue wideValue
            wideAgain    = D.svCastFromFP wideKind rneValue wideAsDouble
            oneAsFloat   = D.svCastToFP KFloat rneValue oneBit
            oneAgain     = D.svCastFromFP oneBitKind rneValue oneAsFloat
            allChecks    = foldl D.svAnd (unSBV nativeChecks) [D.svEqual wideAgain wideValue, D.svEqual oneAgain oneBit]
        svCgReturn allChecks
      halfwayBits = 0x3ff0000010000000
      floatOne    = 0x3f800000
      floatNext   = 0x3f800001
      rneValue    = unSBV sRNE
      wideKind    = KBounded True 673
      oneBitKind  = KBounded False 1
  compileAndRunLibBF dir "nativeFloatWidthConversions" program "= 1"

-- | A separately compiled caller changes the hardware rounding mode around
-- explicitly rounded casts. Check halfway values at native and non-native
-- bit widths, large signed/unsigned integers, and binary64-to-binary32 narrowing.
nativeFloatCastEnvironment :: Assertion
nativeFloatCastEnvironment = withSystemTempDirectory "sbv-native-float-cast-environment" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgGenerateDriver False
        floatBits  <- cgInput "floatBits"     :: SBVCodeGen SWord32
        doubleBits <- cgInput "doubleBits"    :: SBVCodeGen SWord64
        halfBits   <- cgInput "halfBits"      :: SBVCodeGen SWord32
        signed     <- cgInput "signedValue"   :: SBVCodeGen SInt64
        unsigned   <- cgInput "unsignedValue" :: SBVCodeGen SWord64
        let float    = sWord32AsSFloat floatBits
            double   = sWord64AsSDouble doubleBits
            half     = sWord32AsSFloat halfBits
            modes    = [sRNE, sRNA, sRTP, sRTN, sRTZ]
            widths   = [1, 7, 8, 9, 16, 32, 64, 65, 673]
            checks signedKind width = zipWith check modes expected
              where kind     = KBounded signedKind width
                    positive = if width == 1 then half else float
                    value    = if signedKind then negate positive else positive
                    expected
                      | width == 1 = if signedKind then [0, -1, 0, -1, 0] else [0, 1, 1, 0, 0]
                      | signedKind = [-2, -3, -2, -3, -2]
                      | True       = [2, 3, 3, 2, 2]
                    check rm result = D.svEqual (D.svCastFromFP kind (unSBV rm) (unSBV value)) (D.svInteger kind result)
            nativeChecks = sFloatAsSWord32 (toSFloat sRNE double) .== 0x3f800000
                       .&& toSDouble sRNE signed .== -9007199254740992
                       .&& toSFloat sRNE signed .== -9007199254740992
                       .&& toSDouble sRNE unsigned .== 18446744073709551616
                       .&& toSFloat sRNE unsigned .== 18446744073709551616
        svCgReturn (foldl D.svAnd (unSBV nativeChecks) (concat [checks sign width | sign <- [False, True], width <- widths]))
      caller = unlines
        [ "#include <fenv.h>"
        , "#include \"nativeFloatCastEnvironment.h\""
        , "int main(void)"
        , "{"
        , "  const int modes[] = { FE_TONEAREST, FE_UPWARD, FE_DOWNWARD, FE_TOWARDZERO };"
        , "  const int original = fegetround();"
        , "  for (size_t i = 0; i < sizeof modes / sizeof modes[0]; ++i) {"
        , "    if (fesetround(modes[i]) != 0) return 1;"
        , "    if (!nativeFloatCastEnvironment(UINT32_C(0x40200000), UINT64_C(0x3ff0000010000000), UINT32_C(0x3f000000), -INT64_C(9007199254740993), UINT64_MAX)) return 2;"
        , "    if (fegetround() != modes[i]) return 3;"
        , "  }"
        , "  return fesetround(original) != 0;"
        , "}"
        ]
  compileAndRunLibBFCaller dir "nativeFloatCastEnvironment" program caller

-- | SMT leaves non-finite and out-of-range floating-to-bit-vector results
-- unspecified. The backend chooses zero for non-finite inputs and low bits
-- for finite ones, without invoking an overflowing native C integer cast.
nativeFloatExceptionalCasts :: Assertion
nativeFloatExceptionalCasts = mapM_ check [0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0x8000000000000000, 0x7e70000000000000, 0xfe70000000000000]
 where check bits = withSystemTempDirectory "sbv-native-float-exceptional-casts" $ \dir -> do
         let program = do
               cgOverwriteFiles True
               cgSetDriverValues [bits]
               raw <- cgInput "raw" :: SBVCodeGen SWord64
               let value  = sWord64AsSDouble raw
                   values = [unSBV value, unSBV (toSFloat sRNE value)]
                   kinds  = [KBounded sign width | sign <- [False, True], width <- [1, 7, 8, 16, 32, 64, 65, 673]]
                   checks = [D.svEqual (D.svCastFromFP kind (unSBV sRNE) source) (D.svInteger kind 0) | kind <- kinds, source <- values]
               svCgReturn (foldl D.svAnd (unSBV sTrue) checks)
         compileAndRunLibBF dir "nativeFloatExceptionalCasts" program ") = 1"

-- | Exactly representable casts stay native even with symbolic rounding.
-- Include negative zero so widening cannot accidentally change its sign.
nativeExactFloatConversions :: Assertion
nativeExactFloatConversions = withSystemTempDirectory "sbv-exact-native-float-casts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [-32768, 4294967295, 0x80000000, 2]
        small    <- cgInput "small"    :: SBVCodeGen SInt16
        unsigned <- cgInput "word"     :: SBVCodeGen SWord32
        zeroRaw  <- cgInput "zeroBits" :: SBVCodeGen SWord32
        mode     <- cgInput "mode"     :: SBVCodeGen SRoundingMode
        let checks rm = [ toSFloat rm small .== -32768
                        , toSDouble rm unsigned .== 4294967295
                        , sDoubleAsSWord64 (toSDouble rm (sWord32AsSFloat zeroRaw)) .== 0x8000000000000000
                        ]
        cgReturn (sAnd (concatMap checks [sRNE, sRNA, sRTP, sRTN, sRTZ, mode]))
  compileAndRunWith ["-lm"] dir "nativeExactFloatConversions" program ") = 1"
  source <- readFile (dir </> "nativeExactFloatConversions.c")
  makefile <- readFile (dir </> "Makefile")
  assertBool "Exact native conversions must not include LibBF" (not ("<libbf.h>" `isInfixOf` source))
  assertBool "Exact native conversions must not link LibBF" (not ("-lbf" `isInfixOf` makefile))

-- | Exercise LibBF-mediated conversion between native floats and GMP-backed
-- exact numbers without introducing an arbitrary floating-point format.
nativeFloatExactConversions :: Assertion
nativeFloatExactConversions = withSystemTempDirectory "sbv-native-float-exact" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [16777217, 3, 2, 5, 2]
        integer         <- cgInput "integer"         :: SBVCodeGen SInteger
        realNumerator   <- cgInput "realNumerator"   :: SBVCodeGen SReal
        realDenominator <- cgInput "realDenominator" :: SBVCodeGen SReal
        five            <- cgInput "five"            :: SBVCodeGen SFloat
        two             <- cgInput "two"             :: SBVCodeGen SFloat
        let rational      = realNumerator / realDenominator
            integerRNE    = toSFloat sRNE integer
            integerRTP    = toSFloat sRTP integer
            rationalValue = toSDouble sRNE rational
            twoAndAHalf   = fpDiv sRNE five two
            roundedEven   = fromSFloat sRNE twoAndAHalf :: SInteger
            roundedAway   = fromSFloat sRNA twoAndAHalf :: SInteger
            roundedUp     = fromSFloat sRTP twoAndAHalf :: SInteger
            roundedDown   = fromSFloat sRTN twoAndAHalf :: SInteger
            roundedZero   = fromSFloat sRTZ twoAndAHalf :: SInteger
            exactRational = fromSDouble sRNE rationalValue :: SReal
        cgReturn $ integerRNE .== 16777216
               .&& integerRTP .== 16777218
               .&& rationalValue .== 1.5
               .&& roundedEven .== 2
               .&& roundedAway .== 3
               .&& roundedUp   .== 3
               .&& roundedDown .== 2
               .&& roundedZero .== 2
               .&& exactRational .== 3 / 2
  compileAndRunLibBFGMP dir "nativeFloatExactConversions" program "= 1"

-- | Mapped integer casts must use the selected width in both directions while
-- preserving every explicit rounding mode, including halfway negative values.
mappedIntegerFloatConversions :: Assertion
mappedIntegerFloatConversions = mapM_ check [(width, exposeChecks, arbitraryResult) | width <- [8, 16, 32, 64], exposeChecks <- [True, False], arbitraryResult <- [False, True]]
 where check (width, exposeChecks, arbitraryResult) = withSystemTempDirectory "sbv-mapped-integer-float" $ \dir -> do
         let program = do
               cgOverwriteFiles True
               cgIntegerSize width
               cgSetDriverValues [sample, -5, 65539]
               value <- cgInput "value" :: SBVCodeGen SInteger
               five  <- cgInput "five"  :: SBVCodeGen SDouble
               large <- cgInput "large" :: SBVCodeGen SDouble
               let fraction = fpDiv sRNE five 2
                   half rm = toSFloatingPoint rm value :: SFPHalf
                   halfFraction = fpDiv sRNE (toSFloatingPoint sRNE five :: SFPHalf) 2
                   reference rm
                     | width == 8 = 5
                     | True       = ite (rm .== sRNA .|| rm .== sRTP) 2050 2048 :: SFPHalf
                   checks (rm, expected) =
                     [ sFloatingPointAsSWord (half rm) .== sFloatingPointAsSWord (reference rm)
                     , (fromSDouble rm fraction :: SInteger) .== expected
                     , toSDouble rm value .== fromInteger sample
                     ]
                     ++ [(fromSFloatingPoint rm halfFraction :: SInteger) .== expected | arbitraryResult]
                   allChecks = ((fromSDouble sRNE large :: SInteger) .== 65539)
                             : concatMap checks [(sRNE, -2), (sRNA, -3), (sRTP, -2), (sRTN, -3), (sRTZ, -2)]
               if exposeChecks
                  then do cgOutputArr "checks" allChecks
                          cgOutputArr "actual" (map (sFloatingPointAsSWord . half) [sRNE, sRNA, sRTP, sRTN, sRTZ])
                          cgOutputArr "expected" (map (sFloatingPointAsSWord . reference) [sRNE, sRNA, sRTP, sRTN, sRTZ])
                  else pure ()
               cgReturn (sAnd allChecks)
             sample = if width == 8 then 5 else 2049
         compileAndRunLibBF dir "mappedIntegerFloat" program ") = 1"

-- | Native real mappings still require representation-aware conversion:
-- exact integers round to the selected real format, real-to-integer casts
-- floor, and explicit floating casts honor their requested rounding mode.
mappedRealConversions :: Assertion
mappedRealConversions = mapM_ check [(realType, mappedInteger) | realType <- [CgFloat, CgDouble], mappedInteger <- [False, True]]
 where check (realType, mappedInteger) = withSystemTempDirectory "sbv-mapped-real-conversions" $ \dir -> do
         let program = do
               cgOverwriteFiles True
               cgSRealType realType
               if mappedInteger then cgIntegerSize 32 else pure ()
               cgSetDriverValues [16777217, -5, 7]
               value <- cgInput "value" :: SBVCodeGen SInteger
               real  <- cgInput "real"  :: SBVCodeGen SReal
               seven <- cgInput "seven" :: SBVCodeGen SFPHalf
               let expected = case realType of
                                CgFloat -> 16777216
                                _       -> 16777217
                   half = toSFloatingPoint sRTP real :: SFPHalf
               cgReturn $ (sFromIntegral value :: SReal) .== expected
                      .&& sRealToSIntegerFloor (real / 2) .== -3
                      .&& (fromSFloatingPoint sRNE seven :: SReal) .== 7
                      .&& half .== -5
                      .&& toSDouble sRNE real .== -5
         compileAndRunLibBFGMP dir "mappedRealConversions" program "= 1"

-- | Long double retains its native ABI, but cannot be silently treated as an
-- IEEE binary64 value when crossing an exact or arbitrary-float boundary.
longDoubleNumericBoundaries :: Assertion
longDoubleNumericBoundaries = mapM_ check
  [ do value <- cgInput "value" :: SBVCodeGen SInteger
       cgReturn (sFromIntegral value :: SReal)
  , do value <- cgInput "value" :: SBVCodeGen SReal
       cgReturn (sRealToSIntegerFloor value)
  , do value <- cgInput "value" :: SBVCodeGen SFPHalf
       cgReturn (fromSFloatingPoint sRNE value :: SReal)
  , do value <- cgInput "value" :: SBVCodeGen SReal
       cgReturn (toSFloatingPoint sRNE value :: SFPHalf)
  ]
 where check program = withSystemTempDirectory "sbv-long-double-boundary" $ \dir -> do
         result <- try (D.compileToC (Just dir) "longDoubleBoundary" $ do
                          cgSRealType CgLongDouble
                          program) :: IO (Either ErrorCall ())
         case result of
           Left exception -> assertBool (displayException exception) ("CgLongDouble" `isInfixOf` displayException exception)
           Right _        -> assertBool "Expected an unsupported long-double bridge diagnostic" False
         assertEqual "Unsupported bridges must not write files" [] =<< listDirectory dir

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

-- | Exercise LibBF-valued table entries constructed from a structured
-- lambda's parameter and selected entirely inside its retained DAG.
arbitraryFloatLambdaTable :: Assertion
arbitraryFloatLambdaTable = withSystemTempDirectory "sbv-arbitrary-float-lambda-table" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        key <- cgInput "key" :: SBVCodeGen SWord8
        let source = lambdaArray (\index -> select [toFP index, fpAdd sRNE (toFP index) 1] 0 index)
                     :: SArray Word8 (FloatingPoint 15 113)
        cgReturn (sFloatingPointAsSWord (readArray source key) :: SWord 128)
      toFP value = toSFloatingPoint sRNE value :: SFloatingPoint 15 113
      bias       = 2 ^ (14 :: Int) - 1 :: Integer
      twoRaw     = (bias + 1) * 2 ^ (112 :: Int)
  compileAndRunLibBF dir "arbitraryFloatLambdaTable" program (asHex 2 twoRaw)

-- | Exercise correctly rounded conversions between LibBF formats and
-- GMP-backed unbounded integers and rational reals.
arbitraryFloatExactConversions :: Assertion
arbitraryFloatExactConversions = withSystemTempDirectory "sbv-arbitrary-float-exact" $ \dir -> do
  let largeSample = negate (2 ^ (200 :: Int) + 2 ^ (100 :: Int))
      program = do
        cgOverwriteFiles True
        cgSetDriverValues [2049, largeSample, 7, 2, 5, 2]
        integer         <- cgInput "integer"      :: SBVCodeGen SInteger
        largeInteger    <- cgInput "largeInteger" :: SBVCodeGen SInteger
        realNumerator   <- cgInput "numerator"    :: SBVCodeGen SReal
        realDenominator <- cgInput "denominator"  :: SBVCodeGen SReal
        five            <- cgInput "five"         :: SBVCodeGen SFPHalf
        two             <- cgInput "two"          :: SBVCodeGen SFPHalf
        let rational       = realNumerator / realDenominator
            integerRNE     = toSFloatingPoint sRNE integer :: SFPHalf
            integerRTP     = toSFloatingPoint sRTP integer :: SFPHalf
            largeQuad      = toSFloatingPoint sRNE largeInteger :: SFPQuad
            largeRoundTrip = fromSFloatingPoint sRNE largeQuad :: SInteger
            rationalHalf   = toSFloatingPoint sRNE rational :: SFPHalf
            twoAndAHalf    = fpDiv sRNE five two
            roundedEven    = fromSFloatingPoint sRNE twoAndAHalf :: SInteger
            roundedAway    = fromSFloatingPoint sRNA twoAndAHalf :: SInteger
            roundedUp      = fromSFloatingPoint sRTP twoAndAHalf :: SInteger
            roundedDown    = fromSFloatingPoint sRTN twoAndAHalf :: SInteger
            roundedZero    = fromSFloatingPoint sRTZ twoAndAHalf :: SInteger
            exactRational  = fromSFloatingPoint sRNE rationalHalf :: SReal
            integerRNEBits = sFloatingPointAsSWord integerRNE :: SWord 16
            integerRTPBits = sFloatingPointAsSWord integerRTP :: SWord 16
        cgReturn $ integerRNEBits .== 0x6800
               .&& integerRTPBits .== 0x6801
               .&& largeRoundTrip .== largeInteger
               .&& rationalHalf .== 3.5
               .&& roundedEven .== 2
               .&& roundedAway .== 3
               .&& roundedUp   .== 3
               .&& roundedDown .== 2
               .&& roundedZero .== 2
               .&& exactRational .== 7 / 2
  compileAndRunLibBFGMP dir "arbitraryFloatExactConversions" program "= 1"

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

-- | Generate and execute a C program using both LibBF and GMP.
compileAndRunLibBFGMP :: FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRunLibBFGMP dir functionName program expected = do
  (includeDir, archive) <- locateLibBF
  (pkgExit, pkgOutput, pkgError) <- readProcessWithExitCode "pkg-config" ["--cflags", "--libs", "gmp"] ""
  assertEqual pkgError ExitSuccess pkgExit
  compileAndRunWith (["-I" ++ includeDir, archive, "-lm"] ++ words pkgOutput) dir functionName program expected

-- | Generate, compile, and execute C with additional compiler/linker options.
-- @SBV_C_TEST_FLAGS@ supplies extra flags for optimization and sanitizer runs.
compileAndRunWith :: [String] -> FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRunWith ccOptions dir functionName program expected = do
  (_, cfg, bundle) <- compileToC' functionName program
  renderCgPgmBundle (Just dir) (cfg, bundle)

  out <- compileAndRunGenerated ccOptions dir functionName
  assertBool ("Expected generated output to contain " ++ expected ++ ", received:\n" ++ out) (expected `isInfixOf` out)

-- | Exercise a generated native ABI from an independent caller, linked with
-- LibBF. Enable dynamic rounding for callers that modify the floating-point
-- environment; the caller reports failure through its exit status.
compileAndRunLibBFCaller :: FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRunLibBFCaller dir functionName program caller = do
  (includeDir, archive) <- locateLibBF
  (_, cfg, bundle) <- compileToC' functionName program
  renderCgPgmBundle (Just dir) (cfg, bundle)
  writeFile (dir </> functionName ++ "_driver.c") caller
  _ <- compileAndRunGenerated ["-frounding-math", "-I" ++ includeDir, archive, "-lm"] dir functionName
  pure ()

-- | Compile and run an already rendered program and driver. Honor optional
-- optimization and sanitizer flags supplied by @SBV_C_TEST_FLAGS@.
compileAndRunGenerated :: [String] -> FilePath -> String -> IO String
compileAndRunGenerated ccOptions dir functionName = do
  let source = dir </> functionName ++ ".c"
      driver = dir </> functionName ++ "_driver.c"
      exe    = dir </> functionName ++ "_driver"
  extraFlags <- maybe [] words <$> lookupEnv "SBV_C_TEST_FLAGS"
  (ccExit, _, ccErr) <- readProcessWithExitCode "cc" (["-std=c11", "-Wall", "-Werror", source, driver, "-o", exe] ++ extraFlags ++ ccOptions) ""
  assertEqual ccErr ExitSuccess ccExit

  (runExit, out, runErr) <- readProcessWithExitCode exe [] ""
  assertEqual runErr ExitSuccess runExit
  pure out

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
