-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.ScalarSafety
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Executed regressions for diagnostic escaping and mapped real flooring.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.ScalarSafety (tests, testsWith) where

import Control.Monad (void)
import Data.List (isInfixOf)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty.HUnit (assertBool, assertEqual)

import Data.SBV.Tools.CodeGen
import qualified Data.SBV.Tools.CodeGen.Legacy as Legacy
import Utils.SBVTestFramework

-- | Generate a standalone function or a single-component static library.
type Generator = FilePath -> Bool -> SBVCodeGen () -> IO ()

-- | Exercise both public backends with the same scalar safety matrix.
tests :: TestTree
tests = testGroup "CodeGeneration.ScalarSafety"
  [ testsWith "current" $ \dir library program ->
      if library
         then void $ compileToCLib (Just dir) "scalarLibrary" [("scalarChecks", program)]
         else compileToC (Just dir) "scalarChecks" program
  , testsWith "legacy" $ \dir library program ->
      if library
         then void $ Legacy.compileToCLib (Just dir) "scalarLibrary" [("scalarChecks", program)]
         else Legacy.compileToC (Just dir) "scalarChecks" program
  ]

-- | Reuse the same strict-warning, optimization, and sanitizer matrix for a
-- compatibility backend. Independent C callers supply fractional inputs and
-- check against mathematical integer results rather than C casts.
testsWith :: String -> Generator -> TestTree
testsWith groupName generate = testGroup groupName
  [ testGroup (form ++ "/" ++ optimization)
      [ testGroup "floor"
          [ testCase (show realType ++ "/" ++ show width) $ withSystemTempDirectory "sbv-c-real-floor" $ \dir -> do
              executablePath <- compileCaller generate dir library optimization (floorCaller realType width) $ do
                cgSRealType realType
                cgIntegerSize width
                value <- cgInput "value" :: SBVCodeGen SReal
                cgReturn (sRealToSIntegerFloor value)
              makefile <- readFile (dir </> "Makefile")
              assertBool "Flooring must link the standard math library" ("-lm" `isInfixOf` makefile)
              runSuccessfully executablePath
              mapM_ (checkNonFinite executablePath) ["nan", "inf", "negative-inf"]
          | realType <- [CgFloat, CgDouble, CgLongDouble]
          , width <- [8, 16, 32, 64]
          ]
      , testGroup "labels"
          [ testCase sampleName $ withSystemTempDirectory "sbv-c-scalar-label" $ \dir -> do
              executablePath <- compileCaller generate dir library optimization labelCaller $ do
                value <- cgInput "value" :: SBVCodeGen SWord8
                cgReturn (label message value)
              runSuccessfully executablePath
          | (sampleName, message) <- labelSamples
          ]
      , testCase "assertion message" $ withSystemTempDirectory "sbv-c-assertion-text" $ \dir -> do
          let message = "must be \"small\"; %n %s 100% */\n/* \\\n??/ \955"
          executablePath <- compileCaller generate dir library optimization labelCaller $ do
            value <- cgInput "value" :: SBVCodeGen SWord8
            cgReturn (sAssert Nothing message (value .< 5) value)
          (runExit, _, runError) <- readProcessWithExitCode executablePath [] ""
          assertBool "The failed assertion must terminate the caller" (runExit /= ExitSuccess)
          assertBool runError (("ASSERTION FAILED: " ++ message) `isInfixOf` runError)
      ]
  | (form, library) <- [("program", False), ("library", True)]
  , optimization <- ["-O0", "-O2 -fsanitize=undefined,float-cast-overflow -fno-sanitize-recover=all"]
  ]

-- | Text must remain a semantic no-op even when it resembles C statements or
-- affects preprocessing. Embedded NUL/control bytes must also compile cleanly.
labelSamples :: [(String, String)]
labelSamples = [ ("statements", "*/; abort(); /*")
               , ("preprocessing", "nested /* comment; \\\n??/\n*/")
               , ("control characters", "Unicode \955, NUL \0, CR \r, tab \t and control \SOH")
               ]

-- | Generate and build the selected artifact, then link an independent caller.
-- Additional local sanitizer flags apply to both the generated C and caller.
compileCaller :: Generator -> FilePath -> Bool -> String -> String -> SBVCodeGen () -> IO FilePath
compileCaller generate dir library optimization source program = do
  generate dir library $ do
    cgOverwriteFiles True
    cgGenerateDriver False
    program
  extraFlags <- maybe [] words <$> lookupEnv "SBV_C_TEST_FLAGS"
  let flags = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-trigraphs"] ++ words optimization ++ extraFlags
      artifact = if library then "scalarLibrary.a" else "scalarChecks.o"
      header   = if library then "scalarLibrary.h" else "scalarChecks.h"
      executablePath = dir </> "caller"
  (makeExit, _, makeError) <- readProcessWithExitCode "make" ["-C", dir, artifact, "CCFLAGS=" ++ unwords flags] ""
  assertEqual makeError ExitSuccess makeExit
  writeFile (dir </> "caller.c") ("#include \"" ++ header ++ "\"\n" ++ source)
  (ccExit, _, ccError) <- readProcessWithExitCode "cc" (flags ++ [dir </> "caller.c", dir </> artifact, "-lm", "-o", executablePath]) ""
  assertEqual ccError ExitSuccess ccExit
  pure executablePath

-- | Require successful execution, reporting captured diagnostics on failure.
runSuccessfully :: FilePath -> Assertion
runSuccessfully executablePath = do
  (runExit, _, runError) <- readProcessWithExitCode executablePath [] ""
  assertEqual runError ExitSuccess runExit

-- | Non-finite mapped real inputs must fail explicitly before an integer cast.
checkNonFinite :: FilePath -> String -> Assertion
checkNonFinite executablePath sample = do
  (runExit, _, runError) <- readProcessWithExitCode executablePath [sample] ""
  assertBool "Non-finite real flooring must terminate the caller" (runExit /= ExitSuccess)
  assertBool runError ("Cannot floor a non-finite mapped SReal" `isInfixOf` runError)
  assertBool runError (not ("runtime error:" `isInfixOf` runError))

-- | A successful label is observationally identical to its scalar argument.
labelCaller :: String
labelCaller = unlines ["#include <assert.h>", "int main(void) { assert(scalarChecks(7) == 7); return 0; }"]

-- | Supply exact binary fractions, signed boundaries, large finite values,
-- and subnormals. Precision-dependent boundary cases run only when the actual
-- C real representation can distinguish the adjacent integers.
floorCaller :: CgSRealType -> Int -> String
floorCaller realType width = unlines $
  [ "#include <assert.h>"
  , "#include <float.h>"
  , "#define REAL_MANT_DIG " ++ floatMacro "MANT_DIG"
  , "int main(int argc, char **argv)"
  , "{"
  , "  if (argc > 1) {"
  , "    SReal value = argv[1][0] == 'n' ? (argv[1][1] == 'a' ? (SReal) NAN : (SReal) -INFINITY) : (SReal) INFINITY;"
  , "    (void) scalarChecks(value); return 0;"
  , "  }"
  ]
  ++ [check input (floor value) | (input, value) <- samples]
  ++ [ "#if REAL_MANT_DIG >= 32"
     , check "0x7fffffffp0L" (2 ^ (31 :: Int) - 1)
     , "#endif"
     , "#if REAL_MANT_DIG >= 64"
     , check "0xffffffffffffffffp0L" (2 ^ (64 :: Int) - 1)
     , check "-0x8000000000000001p0L" (negate (2 ^ (63 :: Int) + 1))
     , "#endif"
     , check (floatMacro "TRUE_MIN") 0
     , check ("-" ++ floatMacro "TRUE_MIN") (-1)
     , "#if " ++ floatMacro "MAX_EXP" ++ " - REAL_MANT_DIG >= 64"
     , check (floatMacro "MAX") 0
     , check ("-" ++ floatMacro "MAX") 0
     , "#endif"
     , "  return 0;"
     , "}"
     ]
 where floatMacro suffix = case realType of
                             CgFloat      -> "FLT_"  ++ suffix
                             CgDouble     -> "DBL_"  ++ suffix
                             CgLongDouble -> "LDBL_" ++ suffix

       check :: String -> Integer -> String
       check input expected = "  assert(scalarChecks((SReal) (" ++ input ++ ")) == (SInteger) " ++ signedLiteral (wrap expected) ++ ");"
       wrap value = let modulus = 2 ^ width
                        bits    = value `mod` modulus
                    in if bits >= modulus `div` 2 then bits - modulus else bits
       signedLiteral value
         | value == negate (2 ^ (63 :: Int)) = "(-INT64_C(9223372036854775807) - INT64_C(1))"
         | True                             = "INT64_C(" ++ show value ++ ")"

-- | Values exactly representable even by binary32. Integer expectations use
-- arbitrary-precision Haskell arithmetic, independently of the C helper.
samples :: [(String, Rational)]
samples = [ ("0.0L", 0), ("-0.0L", 0)
          , ("2.5L", 5 % 2), ("-2.5L", -(5 % 2))
          , ("0.5L", 1 % 2), ("-0.5L", -(1 % 2))
          , ("127.75L", 511 % 4), ("-128.25L", -(513 % 4))
          , ("255.75L", 1023 % 4), ("-256.25L", -(1025 % 4))
          , ("65535.75L", 262143 % 4), ("-65536.25L", -(262145 % 4))
          , ("0x1p31L", 2 ^ (31 :: Int)), ("-0x1p31L", negate (2 ^ (31 :: Int)))
          , ("0x1p63L", 2 ^ (63 :: Int)), ("-0x1p63L", negate (2 ^ (63 :: Int)))
          , ("0x1p64L", 2 ^ (64 :: Int)), ("-0x1p64L", negate (2 ^ (64 :: Int)))
          , ("0x1p100L", 2 ^ (100 :: Int)), ("-0x1p100L", negate (2 ^ (100 :: Int)))
          , ("(0x1p63L + 0x1p40L)", 2 ^ (63 :: Int) + 2 ^ (40 :: Int))
          , ("(0x1p64L - 0x1p40L)", 2 ^ (64 :: Int) - 2 ^ (40 :: Int))
          , ("(0x1p40L + 0x1p20L)", 2 ^ (40 :: Int) + 2 ^ (20 :: Int))
          ]
