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

import Prelude hiding((++), map)
import qualified Prelude as P

import Data.SBV.List
import Data.SBV.Internals hiding(free_)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Lambda" [
      goldenCapturedIO "lambda1" $ record $ lambda (2 :: SInteger)
    , goldenCapturedIO "lambda2" $ record $ lambda (\x -> x+1 :: SInteger)
    , goldenCapturedIO "lambda3" $ record $ lambda (\x y -> x+y*2 :: SInteger)
    , goldenCapturedIO "lambda4" $ check t1
    ]
  where record :: IO String -> FilePath -> IO ()
        record gen rf = appendFile rf . (P.++ "\n") =<< gen

        check :: Symbolic () -> FilePath -> IO ()
        check t rf = do r <- satWith z3{verbose=True, redirectVerbose=Just rf} t
                        appendFile rf ("\nRESULT:\n" P.++ show r P.++ "\n")

        t1 = do let arg = [1, 2, 3 :: Integer]
                res <- free_
                constrain $ res .== map (\_ -> sFalse) arg

