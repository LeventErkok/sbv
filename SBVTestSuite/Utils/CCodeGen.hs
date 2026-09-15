-----------------------------------------------------------------------------
-- |
-- Module    : Utils.CCodeGen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Shared dependency discovery for generated-C integration tests.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Utils.CCodeGen (locateLibBF, generatedMakeOptions) where

import Control.Exception (IOException, catch)
import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((</>), takeDirectory)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.IO.Unsafe (unsafePerformIO)

-- | Locate the header and static archive installed for the Haskell @libBF@
-- dependency so integration tests exercise the same C implementation.
locateLibBF :: IO (FilePath, FilePath)
locateLibBF = modifyMVar libBFLocation $ \cached -> do
  result <- maybe discoverLibBF pure cached
  pure (Just result, result)

-- | Share immutable dependency discovery across parallel integration tests.
{-# NOINLINE libBFLocation #-}
libBFLocation :: MVar (Maybe (FilePath, FilePath))
libBFLocation = unsafePerformIO (newMVar Nothing)

-- | Allow explicit installations; otherwise find a matching header/archive
-- pair from one Cabal package, never from different package versions.
discoverLibBF :: IO (FilePath, FilePath)
discoverLibBF = do
  includeOverride <- lookupEnv "SBV_C_LIBBF_INCLUDE"
  libraryOverride <- lookupEnv "SBV_C_LIBBF_LIBRARY"
  case (includeOverride, libraryOverride) of
    (Just includeDir, Just archive) -> do
      headerExists <- doesFileExist (includeDir </> "libbf.h")
      archiveExists <- doesFileExist archive
      if headerExists && archiveExists then pure (includeDir, archive)
        else fail "SBV_C_LIBBF_INCLUDE/SBV_C_LIBBF_LIBRARY must name an installed libbf.h and library."
    (Nothing, Nothing) -> discoverStoredLibBF
    _ -> fail "Set both SBV_C_LIBBF_INCLUDE and SBV_C_LIBBF_LIBRARY, or neither."

-- | Discover the installed Haskell dependency's bundled C library.
discoverStoredLibBF :: IO (FilePath, FilePath)
discoverStoredLibBF = do
  (pathExit, pathOutput, pathError) <- readProcessWithExitCode "cabal" ["path"] ""
  case pathExit of
    ExitSuccess -> pure ()
    _ -> fail $ "Unable to query Cabal store: " ++ pathError
  let storePrefix = "compiler-store-path: "
      stores      = [drop (length storePrefix) line | line <- lines pathOutput, storePrefix `isInfixOf` line]
  store <- case stores of
             path:_ -> pure path
             []     -> fail $ "Unable to find Cabal store: " ++ pathError
  packages <- listDirectory store
  let libBFDirs = [store </> entry | entry <- sort packages, "lbBF-" `isPrefixOf` entry]
  firstSuccessful [do header <- findInstalledFile path "libbf.h"
                      archive <- findInstalledFile path "libHSlbBF"
                      pure (takeDirectory header, archive)
                  | path <- libBFDirs]

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

-- | Build generated Makefiles with strict warnings, resolving LibBF from the
-- Cabal store when needed. Keep compiler overrides and GMP discovery intact.
-- Append @SBV_C_TEST_FLAGS@ to both compilation and linking commands, allowing
-- optimization and sanitizer runs to cover generated programs and library callers.
generatedMakeOptions :: FilePath -> IO [String]
generatedMakeOptions dir = do
  makefile <- readFile (dir </> "Makefile")
  extraFlags <- maybe "" (" " ++) <$> lookupEnv "SBV_C_TEST_FLAGS"
  let flags = "CCFLAGS=-std=c11 -Wall -Werror -O2" ++ extraFlags
  if "-lbf" `isInfixOf` makefile
    then do (includeDir, archive) <- locateLibBF
            pure [flags ++ " -I\"" ++ includeDir ++ "\"", "SBV_LIBS=\"" ++ archive ++ "\" -lm ${GMP_LIBS}"]
    else pure [flags]
