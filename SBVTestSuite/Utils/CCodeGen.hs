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
import Data.List (isInfixOf, isPrefixOf, isSuffixOf)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath ((</>), takeDirectory)
import System.Process (readProcessWithExitCode)

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

-- | Build generated Makefiles with strict warnings, resolving LibBF from the
-- Cabal store when needed. Keep compiler overrides and GMP discovery intact.
generatedMakeOptions :: FilePath -> IO [String]
generatedMakeOptions dir = do
  makefile <- readFile (dir </> "Makefile")
  if "-lbf" `isInfixOf` makefile
    then do (includeDir, archive) <- locateLibBF
            pure [flags ++ " -I\"" ++ includeDir ++ "\"", "LDFLAGS=\"" ++ archive ++ "\" -lm ${GMP_LIBS}"]
    else pure [flags]
 where flags = "CCFLAGS=-std=c11 -Wall -Werror -O2"
