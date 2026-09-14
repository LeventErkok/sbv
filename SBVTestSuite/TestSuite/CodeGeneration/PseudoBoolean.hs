-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.PseudoBoolean
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Executed pseudo-Boolean comparisons at native overflow boundaries.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.PseudoBoolean (tests, testsWith) where

import Control.Monad (replicateM, void)
import Data.List (intercalate)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty.HUnit (assertEqual)

import Data.SBV.Tools.CodeGen
import qualified Data.SBV.Tools.CodeGen.Legacy as Legacy
import Utils.SBVTestFramework

-- | Exercise both backends through their public standalone and library APIs.
tests :: TestTree
tests = testGroup "CodeGeneration.PseudoBoolean"
  [ testsWith "current" $ \dir library functionName program ->
      if library
         then void $ compileToCLib (Just dir) "pbLibrary" [(functionName, program)]
         else compileToC (Just dir) functionName program
  , testsWith "legacy" $ \dir library functionName program ->
      if library
         then void $ Legacy.compileToCLib (Just dir) "pbLibrary" [(functionName, program)]
         else Legacy.compileToC (Just dir) functionName program
  ]

-- | Reuse the execution matrix for a compatibility backend without changing its
-- import facade. Every truth assignment is checked against unbounded Haskell
-- arithmetic, at both optimization levels and with undefined-behavior checking.
testsWith :: String -> (FilePath -> Bool -> String -> SBVCodeGen () -> IO ()) -> TestTree
testsWith groupName generate = testGroup groupName
  [ testCase (form ++ " mapped" ++ show integerWidth ++ " " ++ optimization) $ withSystemTempDirectory "sbv-c-pseudo-boolean" $ \dir -> do
      let functionName = "pbChecks"
          artifact = if library then "pbLibrary.a" else functionName ++ ".o"
          header   = if library then "pbLibrary.h" else functionName ++ ".h"
      generate dir library functionName $ do
        cgOverwriteFiles True
        cgGenerateDriver False
        cgIntegerSize integerWidth
        inputs <- cgInputArr 5 "inputs"
        cgOutputArr "checks" (comparisons inputs)
      extraFlags <- maybe [] words <$> lookupEnv "SBV_C_TEST_FLAGS"
      let flags = ["-std=c11", "-Wall", "-Wextra", "-Werror"] ++ words optimization ++ extraFlags
      (makeExit, _, makeError) <- readProcessWithExitCode "make"
        ["-C", dir, artifact, "CCFLAGS=" ++ unwords flags] ""
      assertEqual makeError ExitSuccess makeExit
      writeFile (dir </> "caller.c") (caller header functionName)
      let executablePath = dir </> "caller"
      (ccExit, _, ccError) <- readProcessWithExitCode "cc"
        (flags ++ [dir </> "caller.c", dir </> artifact, "-o", executablePath]) ""
      assertEqual ccError ExitSuccess ccExit
      (runExit, _, runError) <- readProcessWithExitCode executablePath [] ""
      assertEqual runError ExitSuccess runExit
      mapM_ (\values -> assertEqual "Concrete SBV comparisons must agree with mathematical sums"
                                    (map Just (expected values)) (map unliteral (comparisons (map literal values)))) assignments
  | (form, library) <- [("standalone", False), ("library", True)]
  , integerWidth <- [8, 64]
  , optimization <- ["-O0", "-O2", "-O1 -fsanitize=undefined -fno-sanitize-recover=all"]
  ]

-- | Coefficients and bounds covering signed 32-bit overflow, signed and unsigned
-- 64-bit overflow, zero weights, exact ties, and crossing a bound late in a sum.
scenarios :: [([Int], Int)]
scenarios = [ ([2000000000, 2000000000, 0, 0, 0], 2100000000)
            , ([maxBound, maxBound, 0, 0, 0], maxBound)
            , (replicate 5 maxBound, maxBound)
            , ([maxBound, 1, maxBound, 1, 0], maxBound)
            , ([0, 0, 0, 0, 0], 0)
            , ([0, 1, 0, 1, 0], 0)
            , ([1, 2, 3, 4, 5], 7)
            , ([1, 2, 3, 4, 5], maxBound)
            , ([maxBound, maxBound, maxBound, 0, 0], 0)
            , ([maxBound - 1, 1, 1, maxBound - 1, 1], maxBound)
            ]

-- | All assignments to the five independent input Booleans.
assignments :: [[Bool]]
assignments = replicateM 5 [False, True]

-- | Exercise all six pseudo-Boolean operators, plus their empty-list semantics.
comparisons :: [SBool] -> [SBool]
comparisons inputs = concat [let weighted = zip coefficients inputs
                            in [pbLe weighted bound, pbGe weighted bound, pbEq weighted bound]
                            | (coefficients, bound) <- scenarios]
                  ++ [pbAtMost inputs 2, pbAtLeast inputs 2, pbExactly inputs 2]
                  ++ [pbAtMost [] 0, pbAtLeast [] 1, pbExactly [] 0]

-- | Compute expected answers with mathematical integers, never machine sums.
expected :: [Bool] -> [Bool]
expected inputs = concat [compareSum (sum [toInteger coefficient | (coefficient, True) <- zip coefficients inputs]) (toInteger bound)
                         | (coefficients, bound) <- scenarios]
               ++ compareSum (toInteger (length (filter id inputs))) 2
               ++ [True, False, True]
 where compareSum total bound = [total <= bound, total >= bound, total == bound]

-- | An independent C caller supplies all input combinations and exact expected
-- outputs. Its arrays are shared across calls to check that temporary sums reset.
caller :: String -> String -> String
caller header functionName = unlines
  [ "#include <assert.h>"
  , "#include \"" ++ header ++ "\""
  , "int main(void)"
  , "{"
  , "  static const SBool inputs[][5] = {" ++ intercalate ", " (map row assignments) ++ "};"
  , "  static const SBool expected[][" ++ show count ++ "] = {" ++ intercalate ", " (map (row . expected) assignments) ++ "};"
  , "  SBool output[" ++ show count ++ "];"
  , "  for (size_t i = 0; i < sizeof inputs / sizeof inputs[0]; ++i) {"
  , "    " ++ functionName ++ "(inputs[i], output);"
  , "    for (size_t j = 0; j < " ++ show count ++ "; ++j) assert(output[j] == expected[i][j]);"
  , "  }"
  , "  return 0;"
  , "}"
  ]
 where count = length (expected (replicate 5 False))
       row values = "{" ++ intercalate ", " [if value then "true" else "false" | value <- values] ++ "}"
