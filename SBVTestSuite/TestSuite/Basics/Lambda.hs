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

{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Lambda(tests)  where

import Prelude hiding((++), map, foldl, sum)
import qualified Prelude as P

import Data.SBV.List
import Data.SBV.Internals hiding(free_)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Lambda" [
      goldenCapturedIO "lambda1" $ record $ lambdaTop (2 :: SInteger)
    , goldenCapturedIO "lambda2" $ record $ lambdaTop (\x -> x+1 :: SInteger)
    , goldenCapturedIO "lambda3" $ record $ lambdaTop (\x y -> x+y*2 :: SInteger)
    , goldenCapturedIO "lambda4" $ check t1
    , goldenCapturedIO "lambda5" $ check t2
    , goldenCapturedIO "lambda6" $ check t3
    , goldenCapturedIO "lambda7" $ check t4
    ]
  where record :: IO String -> FilePath -> IO ()
        record gen rf = appendFile rf . (P.++ "\n") =<< gen

        check :: Symbolic () -> FilePath -> IO ()
        check t rf = do r <- satWith z3{verbose=True, redirectVerbose=Just rf} t
                        appendFile rf ("\nRESULT:\n" P.++ show r P.++ "\n")

        t1 = do let arg = [1, 2, 3 :: Integer]
                res <- free_
                constrain $ res .== map (const sFalse) arg

        t2 = do let arg = [1 .. 5 :: Integer]
                res <- free_
                constrain $ res .== (map (+1) . map (+2)) arg

        t3 = do let arg = [1 .. 5 :: Integer]
                res <- free_
                constrain $ res .== map f arg
          where f x = P.sum [x.^i | i <- [literal i | i <- [1..10 :: Integer]]]

        t4 = do let arg = [[1..5], [1..10], [1..20]] :: SList [Integer]
                res <- free_
                let sum = foldl (+) 0
                constrain $ res .== sum (map sum arg)

{-# ANN module ("HLint: ignore Use map once" :: String) #-}
{-# ANN module ("HLint: ignore Use sum"      :: String) #-}
