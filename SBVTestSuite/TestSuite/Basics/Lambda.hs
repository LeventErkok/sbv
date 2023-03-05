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

import Prelude hiding((++), map, foldl, foldr, sum, length, zip, zipWith, all, any)
import qualified Prelude as P

import Control.Monad (unless)

import Data.SBV.Control
import Data.SBV.Internals hiding(free_)

import Data.SBV.List
import Data.SBV.Tuple

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Lambda" [
      goldenCapturedIO "lambda01" $ record $ lambdaTop (2 :: SInteger)
    , goldenCapturedIO "lambda02" $ record $ lambdaTop (\x -> x+1 :: SInteger)
    , goldenCapturedIO "lambda03" $ record $ lambdaTop (\x y -> x+y*2 :: SInteger)
    , goldenCapturedIO "lambda04" $ eval1 [1 .. 3 :: Integer] (map (const sFalse),  P.map (const False))
    , goldenCapturedIO "lambda05" $ eval1 [1 .. 5 :: Integer] (map (+1) . map (+2), P.map (+1) . P.map (+2))
    , goldenCapturedIO "lambda06" $ eval1 [1 .. 5 :: Integer]
                                          ( map   (\x -> P.sum [x .^ literal i | i <- [1..10 :: Integer]])
                                          , P.map (\x -> P.sum [x  ^ i         | i <- [1..10 :: Integer]])
                                          )

    , goldenCapturedIO "lambda07" $ eval1 ([[1..5], [1..10], [1..20]] :: [[Integer]])
                                          ( let sum = foldl (+) 0 in   sum .   map   sum
                                          ,                          P.sum . P.map P.sum
                                          )

    , goldenCapturedIO "lambda08" $ t5
    , goldenCapturedIO "lambda09" $ t6

    , goldenCapturedIO "lambda10" $ eval1 [1 .. 5 :: Integer] (map (+1), P.map (+1))
    , goldenCapturedIO "lambda11" $ eval1 [1 .. 5 :: Word8]   (map (+1), P.map (+1))

    , goldenCapturedIO "lambda12" $ eval1 [1 .. 3 :: Integer] (map singleton, P.map (\x -> [x]))

    , goldenCapturedIO "lambda13" $ eval1 [(x, y) | x <- [1..3], y <- [4..6 :: Integer]]
                                          (map (\t -> t^._1 + t^._2), P.map (uncurry (+)))
    ]
  where record :: IO String -> FilePath -> IO ()
        record gen rf = appendFile rf . (P.++ "\n") =<< gen

        t5 rf = runSMTWith z3{verbose=True, redirectVerbose=Just rf} $ do

                   let expecting = 5 :: Integer

                   a :: SList Integer <- sList_
                   b :: SList Integer <- sList_

                   query $ do

                     constrain $ length (zip a b) .== literal expecting
                     constrain $ length a .== literal expecting
                     constrain $ length b .== literal expecting
                     constrain $ all (.== 1) a
                     constrain $ all (.== 2) b

                     cs <- checkSat
                     case cs of
                       Sat -> do av <- getValue a
                                 bv <- getValue b
                                 let len = P.fromIntegral $ P.length (P.zip av bv)

                                 unless (len == expecting) $
                                    error $ unlines [ "Bad output:"
                                                    , "  a       = " P.++ show av
                                                    , "  b       = " P.++ show bv
                                                    , "  zip a b = " P.++ show (P.zip av bv)
                                                    , "  Length  = " P.++ show len P.++ " was expecting: " P.++ show expecting
                                                    ]

                       _ -> error $ "Unexpected output: " P.++ show cs

        t6 rf = runSMTWith z3{verbose=True, redirectVerbose=Just rf} $ do

                   a :: SList [Integer] <- sList_

                   sumVal <- sInteger_

                   query $ do

                     let expecting = 5

                     constrain $ a .== literal (replicate expecting (replicate expecting 1))
                     let sum = foldl (+) 0

                     constrain $ sumVal .== sum (map sum a)  -- Must be expecting * expecting

                     cs <- checkSat
                     case cs of
                       Sat -> do final <- getValue sumVal
                                 av    <- getValue a

                                 unless (final == fromIntegral (expecting * expecting)) $
                                    error $ unlines [ "Bad output:"
                                                    , "  a     = " P.++ show av
                                                    , "  Final = " P.++ show final P.++ " was expecting: " P.++ show (expecting*expecting)
                                                    ]

                       _ -> error $ "Unexpected output: " P.++ show cs

eval1 :: (SymVal a, SymVal b, Show a, Show b, Eq b) => a -> (SBV a -> SBV b, a -> b) -> FilePath -> IO ()
eval1 cArg (sFun, cFun) rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                                appendFile rf ("\nRESULT:\n" P.++ showModel z3 m P.++ "\n")

 where run = do arg <- free_
                res <- free_
                constrain $ arg .== literal cArg
                constrain $ res .== sFun arg

                let concResult = cFun cArg

                query $ do
                  cs <- checkSat
                  case cs of
                    Sat -> do resV <- getValue res
                              unless (resV == concResult) $
                                  error $ unlines [ "Bad output:"
                                                  , "  arg      = " P.++ show cArg
                                                  , "  concrete = " P.++ show concResult
                                                  , "  symbolic = " P.++ show resV
                                                  ]
                              getModel
                    _ -> error $ "Unexpected output: " P.++ show cs


{-# ANN module ("HLint: ignore Use map once" :: String) #-}
{-# ANN module ("HLint: ignore Use sum"      :: String) #-}
