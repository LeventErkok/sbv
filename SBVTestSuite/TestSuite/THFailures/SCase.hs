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

import Test.Tasty.Golden
import System.Exit
import System.Process
import System.Directory (withCurrentDirectory)
import qualified Data.ByteString.Lazy.Char8 as BL

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

        args     =  "-XHaskell2010 -fforce-recomp -tmpdir /tmp -outputdir /tmp"
                 ++ concat [" -package " ++ pkg | pkg <- packages]

        compileFail path = do
           (exitCode, _stdout, stderr) <- withCurrentDirectory pre $ readProcessWithExitCode "ghc" (words args ++ [path]) ""
           case exitCode of
             ExitSuccess   -> return $ BL.pack "Expected failure, but compilation succeeded.\n"
             ExitFailure _ -> return $ BL.pack stderr

tests :: TestTree
tests =
  testGroup "THFailures.SCase"
   [ mkCase "SCase01"
   ]
