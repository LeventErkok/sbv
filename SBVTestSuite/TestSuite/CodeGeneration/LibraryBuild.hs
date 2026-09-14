-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.LibraryBuild
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Incremental build regressions for generated C static libraries.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.LibraryBuild (tests, testsWith) where

import Control.Monad (void)
import qualified Data.ByteString as BS
import System.Directory (doesFileExist)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), takeExtension)
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty.HUnit (assertBool, assertEqual)

import Data.SBV.Tools.CodeGen
import Utils.SBVTestFramework

-- | Generate a library named @buildLibrary@ with the supplied components.
type LibraryGenerator = FilePath -> [(String, SBVCodeGen ())] -> IO ()

-- | Exercise the default public library generator.
tests :: TestTree
tests = testsWith "CodeGeneration.LibraryBuild" $ \dir components ->
  void $ compileToCLib (Just dir) "buildLibrary" components

-- | Apply the same archive and driver checks to either public C backend.
testsWith :: String -> LibraryGenerator -> TestTree
testsWith groupName generate = testGroup groupName
  [ testCase "driver archive dependency" (driverDependencies generate)
  , testCase "remove retired components with a driver" (archiveRegeneration generate True)
  , testCase "remove retired components without a driver" (archiveRegeneration generate False)
  , testCase "preserve archive after a failed rebuild" (failedArchiveRebuild generate)
  ]

-- | Generate a trivial scalar component with predictable driver output.
component :: Bool -> Word8 -> SBVCodeGen ()
component driver value = do
  cgOverwriteFiles True
  cgGenerateDriver driver
  cgSetDriverValues []
  cgReturn (literal value)

-- | Building the driver directly must first build its archive, including in
-- parallel builds. Both archive and component changes must invalidate it.
driverDependencies :: LibraryGenerator -> Assertion
driverDependencies generate = withSystemTempDirectory "sbv-c-library-driver" $ \dir -> do
  generate dir [("component", component True 7)]
  build dir ["-j2", "buildLibrary_driver"]
  (runExit, _, runError) <- readProcessWithExitCode (dir </> "buildLibrary_driver") [] ""
  assertEqual runError ExitSuccess runExit
  (freshExit, _, freshError) <- readProcessWithExitCode "make" ["-C", dir, "-q", "buildLibrary_driver"] ""
  assertEqual freshError ExitSuccess freshExit
  mapM_ (checkDependency dir) ["component.c", "buildLibrary.a", "buildLibrary.h"]
 where checkDependency dir prerequisite = do
         (staleExit, _, staleError) <- readProcessWithExitCode "make"
           ["-C", dir, "-q", "-W", prerequisite, "buildLibrary_driver"] ""
         assertEqual (prerequisite ++ ": " ++ staleError) (ExitFailure 1) staleExit

-- | Regeneration must replace the archive's membership, not merely update
-- members still present. Old component files outside the archive are retained.
archiveRegeneration :: LibraryGenerator -> Bool -> Assertion
archiveRegeneration generate driver = withSystemTempDirectory "sbv-c-library-regeneration" $ \dir -> do
  let retained = ("retained", component driver 11)
      retired  = ("retired",  component driver 22)
  generate dir [retained, retired]
  build dir ["buildLibrary.a"]
  checkMembers dir ["retained.o", "retired.o"]
  generate dir [retained]
  build dir ["-B", "buildLibrary.a"]
  checkMembers dir ["retained.o"]
  assertBool "Unselected component objects must not be deleted" =<< doesFileExist (dir </> "retired.o")
  generate dir [retired, retained]
  build dir ["-B", "buildLibrary.a"]
  checkMembers dir ["retired.o", "retained.o"]

-- | An unsuccessful archiver must leave the previous valid archive intact.
-- A subsequent successful rebuild must recover without manual cleanup.
failedArchiveRebuild :: LibraryGenerator -> Assertion
failedArchiveRebuild generate = withSystemTempDirectory "sbv-c-library-failed-rebuild" $ \dir -> do
  generate dir [("component", component False 7)]
  build dir ["buildLibrary.a"]
  original <- BS.readFile (dir </> "buildLibrary.a")
  makeOptions <- buildOptions
  (failedExit, _, _) <- readProcessWithExitCode "make"
    (["-C", dir, "-B", "buildLibrary.a", "AR=false"] ++ makeOptions) ""
  assertBool "The failed archiver must fail the build" (failedExit /= ExitSuccess)
  assertBool "The previous archive must still exist" =<< doesFileExist (dir </> "buildLibrary.a")
  assertEqual "The previous archive must remain unchanged" original =<< BS.readFile (dir </> "buildLibrary.a")
  build dir ["-B", "buildLibrary.a"]
  checkMembers dir ["component.o"]

-- | Build with strict C warnings and optional local sanitizer flags.
build :: FilePath -> [String] -> Assertion
build dir targets = do
  makeOptions <- buildOptions
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ targets ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit

-- | Preserve caller-selected instrumentation during compilation and linking.
buildOptions :: IO [String]
buildOptions = do
  extraFlags <- maybe "" (" " ++) <$> lookupEnv "SBV_C_TEST_FLAGS"
  pure ["CCFLAGS=-std=c11 -Wall -Wextra -Werror -O2" ++ extraFlags]

-- | Compare object membership and order, ignoring platform-specific symbol
-- index members such as the BSD archiver's @__.SYMDEF@ entry.
checkMembers :: FilePath -> [String] -> Assertion
checkMembers dir expected = do
  (arExit, members, arError) <- readProcessWithExitCode "ar" ["t", dir </> "buildLibrary.a"] ""
  assertEqual arError ExitSuccess arExit
  assertEqual "Archive components" expected (filter ((== ".o") . takeExtension) (lines members))
