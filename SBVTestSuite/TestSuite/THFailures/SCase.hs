-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.THFailures.SCase
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing TH failure messages
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.THFailures.SCase(tests) where

import Utils.SBVTestFramework

import Control.Exception (evaluate)
import System.Exit
import System.Process
import Test.Tasty.Golden

import System.IO hiding (stderr)
import System.IO.Temp (withSystemTempDirectory)

import qualified Data.ByteString.Lazy.Char8 as BL

-- | Like readProcessWithExitCode, but in a given directory
readProcessInDir :: FilePath -> String -> [String] -> String -> IO (ExitCode, String, String)
readProcessInDir dir cmd args input = do
    let cp = (proc cmd args)
                { cwd     = Just dir
                , std_in  = CreatePipe
                , std_out = CreatePipe
                , std_err = CreatePipe
                }
    withCreateProcess cp $ \mIn mOut mErr ph -> do
        -- feed input if needed
        case mIn of
            Just hin -> hPutStr hin input >> hClose hin
            Nothing  -> return ()

        out <- case mOut of
            Just hout -> do
                s <- hGetContents hout
                _ <- evaluate (length s)  -- force full read
                return s
            Nothing -> return ""

        err <- case mErr of
            Just herr -> do
                s <- hGetContents herr
                _ <- evaluate (length s)  -- force full read
                return s
            Nothing -> return ""

        exitCode <- waitForProcess ph
        return (exitCode, out, err)

-- | Make a compilation test
mkCase :: TestName -> TestTree
mkCase nm = goldenVsStringDiff nm diffCmd (pre ++ nm ++ ".stderr") (compileFail (nm ++ ".hs"))
  where pre = "SBVTestSuite/TestSuite/THFailures/Files/"

        diffCmd ref new = ["diff", "-u", ref, new]

        packages = [ "QuickCheck"
                   , "array"
                   , "containers"
                   , "deepseq"
                   , "libBF"
                   , "mtl"
                   , "random"
                   , "syb"
                   , "template-haskell"
                   , "text"
                   , "time"
                   , "transformers"
                   , "uniplate"
                   ]

        args td  =  "-XHaskell2010 -fforce-recomp -tmpdir " ++ td ++ " -outputdir " ++ td
                 ++ concat [" -package " ++ pkg | pkg <- packages]

        compileFail path = withSystemTempDirectory "SBVTempDir" $ \tmpDir -> do
           (exitCode, _stdout, stderr) <- readProcessInDir pre "ghc" (words (args tmpDir) ++ [path]) ""
           case exitCode of
             ExitSuccess   -> return $ BL.pack "Expected failure, but compilation succeeded.\n"
             ExitFailure _ -> return $ BL.pack stderr

tests :: TestTree
tests =
  testGroup "THFailures.SCase"
   [ mkCase "SCase01"
   , mkCase "SCase02"
   , mkCase "SCase03"
   , mkCase "SCase04"
   , mkCase "SCase05"
   ]
