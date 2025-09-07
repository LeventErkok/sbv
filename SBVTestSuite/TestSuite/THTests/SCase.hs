-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.THTests.SCase
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing TH messages
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.THTests.SCase(tests) where

import Utils.SBVTestFramework

import Control.Exception (evaluate)
import System.Exit
import System.Process
import Test.Tasty.Golden

import System.IO hiding (stderr, stdout)
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
mkCase nm = goldenVsStringDiff nm diffCmd (pre ++ nm ++ ".stderr") (compile (nm ++ ".hs"))
  where pre = "SBVTestSuite/TestSuite/THTests/Files/"

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

        compile path = withSystemTempDirectory "SBVTempDir" $ \tmpDir -> do
           (exitCode, stdout, stderr) <- readProcessInDir pre "ghc" (words (args tmpDir) ++ [path]) ""
           case exitCode of
             ExitSuccess   -> return $ BL.pack stdout
             ExitFailure _ -> return $ BL.pack stderr

tests :: TestTree
tests = testGroup "THTests.SCase" $ [ mkCase $ "SCase" ++ sh2 i | i <- [(1::Int) .. sCaseTestCnt] ]
  where sCaseTestCnt = 17
        sh2 i | i < 10 = '0' : show i
              | True   =       show i
