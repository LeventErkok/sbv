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
  , testCase "compile and execute special arithmetic" arbitraryFloatSpecialArithmetic
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
