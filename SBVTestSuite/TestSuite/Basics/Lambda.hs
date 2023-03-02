-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test lambda generation
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Lambda(tests)  where

import Data.SBV.Internals

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Lambda" [
      goldenCapturedIO "lambda1" $ record $ lambda (2 :: SInteger)
    , goldenCapturedIO "lambda2" $ record $ lambda (\x -> x+1 :: SInteger)
    , goldenCapturedIO "lambda3" $ record $ lambda (\x y -> x+y*2 :: SInteger)
    ]
  where record :: IO String -> FilePath -> IO ()
        record gen rf = appendFile rf . (++ "\n") =<< gen
