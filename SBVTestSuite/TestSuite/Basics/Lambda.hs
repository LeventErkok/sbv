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

import Prelude hiding((++), map, foldl, foldr, sum, length, zip, zipWith, all, any, concat, filter)
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
  testGroup "Basics.Lambda" $ [
        goldenCapturedIO "lambda01" $ record $ \st -> lambda st (2 :: SInteger)
      , goldenCapturedIO "lambda02" $ record $ \st -> lambda st (\x -> x+1 :: SInteger)
      , goldenCapturedIO "lambda03" $ record $ \st -> lambda st (\x y -> x+y*2 :: SInteger)
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

      , goldenCapturedIO "lambda08" $ eval1 [1 .. 5 :: Float]   (map (+1), P.map (+1))
      , goldenCapturedIO "lambda09" $ eval1 [1 .. 5 :: Int8]    (map (+1), P.map (+1))
      , goldenCapturedIO "lambda10" $ eval1 [1 .. 5 :: Integer] (map (+1), P.map (+1))
      , goldenCapturedIO "lambda11" $ eval1 [1 .. 5 :: Word8]   (map (+1), P.map (+1))

      , goldenCapturedIO "lambda12" $ eval1 [1 .. 3 :: Integer] (map singleton, P.map (: []))

      , goldenCapturedIO "lambda13" $ eval1 [(x, y) | x <- [1..3], y <- [4..6 :: Integer]]
                                            (map (\t -> t^._1 + t^._2), P.map (uncurry (+)))

      , goldenCapturedIO "lambda14" $ eval1 [1 .. 5 :: Integer] (mapi (+) 10, P.zipWith (+) [10..])

      , goldenCapturedIO "lambda15" $ eval1 [1 .. 5 :: Integer] (foldl (+) 0, P.sum)
      , goldenCapturedIO "lambda16" $ eval1 [1 .. 5 :: Integer] (foldl (*) 1, P.product)
      , goldenCapturedIO "lambda17" $ eval1 [1 .. 5 :: Integer]
                                           (   foldl (\soFar elt -> singleton elt ++ soFar) []
                                           , P.foldl (\soFar elt ->           elt :  soFar) []
                                           )

      , goldenCapturedIO "lambda18" $ eval1 [1 .. 5 :: Integer]
                                            (   foldli (\i b a    -> i+b+a) 10 0
                                            , P.foldl  (\b (i, a) -> i+b+a)  0 . P.zip [10..]
                                            )

      , goldenCapturedIO "lambda19" $ eval1 [1 .. 5 :: Integer] (foldr (+) 0, P.foldr (+) 0)
      , goldenCapturedIO "lambda20" $ eval1 [1 .. 5 :: Integer] (foldr (*) 1, P.foldr (*) 1)
      , goldenCapturedIO "lambda21" $ eval1 [1 .. 5 :: Integer]
                                           (   foldr (\elt soFar -> soFar   ++ singleton elt) []
                                           , P.foldr (\elt soFar -> soFar P.++ [elt])         []
                                           )

      , goldenCapturedIO "lambda22" $ eval2 [1 .. 10 :: Integer] [11..20 :: Integer] (zip, P.zip)
      , goldenCapturedIO "lambda23" $ eval2 [1 .. 10 :: Integer] [10, 9 .. 1 :: Integer]
                                            ( \a b ->   foldr (+) 0 (  map (\t -> t^._1+t^._2::SInteger) (  zip a b))
                                            , \a b -> P.foldr (+) 0 (P.map (\t -> fst t+snd t::Integer ) (P.zip a b))
                                            )
      , goldenCapturedIO "lambda24" $ eval2 [1 .. 10 :: Integer] [11..20 :: Integer] (zipWith (+), P.zipWith (+))
      , goldenCapturedIO "lambda25" $ eval2 [1 .. 10 :: Integer] [10, 9 .. 1 :: Integer]
                                            ( \a b ->   foldr (+) 0 (  zipWith (+) a b)
                                            , \a b -> P.foldr (+) 0 (P.zipWith (+) a b)
                                            )

      , goldenCapturedIO "lambda26" $ eval1 ([[1..5], [1..10], [1..20]] :: [[Integer]]) (concat, P.concat)

      , goldenCapturedIO "lambda27" $ eval1 [2, 4, 6,    8, 10 :: Integer] (all (\x -> x `sMod` 2 .== 0), P.all (\x -> x `mod` 2 == 0))
      , goldenCapturedIO "lambda28" $ eval1 [2, 4, 6, 1, 8, 10 :: Integer] (all (\x -> x `sMod` 2 .== 0), P.all (\x -> x `mod` 2 == 0))

      , goldenCapturedIO "lambda29" $ eval1 [2, 4, 6,    8, 10 :: Integer] (any (\x -> x `sMod` 2 ./= 0), P.any (\x -> x `mod` 2 /= 0))
      , goldenCapturedIO "lambda30" $ eval1 [2, 4, 6, 1, 8, 10 :: Integer] (any (\x -> x `sMod` 2 .== 0), P.any (\x -> x `mod` 2 == 0))

      , goldenCapturedIO "lambda31" $ eval1 [1 .. 10 :: Integer] (filter (\x -> x `sMod` 2 .== 0), P.filter (\x -> x `mod` 2 == 0))
      , goldenCapturedIO "lambda32" $ eval1 [1 .. 10 :: Integer] (filter (\x -> x `sMod` 2 ./= 0), P.filter (\x -> x `mod` 2 /= 0))

      , goldenCapturedIO "lambda33" $ record $ \st -> lambda st (0           :: SInteger)
      , goldenCapturedIO "lambda34" $ record $ \st -> lambda st (\x   -> x+1 :: SInteger)
      , goldenCapturedIO "lambda35" $ record $ \st -> lambda st (\x y -> x+y :: SInteger)
      , goldenCapturedIO "lambda36" $ record $ \st -> axiom  st sTrue
      , goldenCapturedIO "lambda37" $ record $ \st -> axiom  st sNot
      , goldenCapturedIO "lambda38" $ record $ \st -> axiom  st (\x y -> x .== (0 :: SInteger) .|| y)
      ]
   P.++ qc1 "lambdaQC" P.sum (foldr (+) (0::SInteger))
  where record :: (State -> IO String) -> FilePath -> IO ()
        record gen rf = do st <- mkNewState defaultSMTCfg (Lambda 0)
                           appendFile rf . (P.++ "\n") =<< gen st

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

eval2 :: (SymVal a, SymVal b, SymVal c, Eq c, Show a, Show b, Show c) => a -> b -> (SBV a -> SBV b -> SBV c, a -> b -> c) -> FilePath -> IO ()
eval2 cArg1 cArg2 (sFun, cFun) rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                                       appendFile rf ("\nRESULT:\n" P.++ showModel z3 m P.++ "\n")

 where run = do arg1 <- free_
                arg2 <- free_
                res <- free_
                constrain $ arg1 .== literal cArg1
                constrain $ arg2 .== literal cArg2
                constrain $ res  .== sFun arg1 arg2

                let concResult = cFun cArg1 cArg2

                query $ do
                  cs <- checkSat
                  case cs of
                    Sat -> do resV <- getValue res
                              unless (resV == concResult) $
                                  error $ unlines [ "Bad output:"
                                                  , "  arg1     = " P.++ show cArg1
                                                  , "  arg2     = " P.++ show cArg2
                                                  , "  concrete = " P.++ show concResult
                                                  , "  symbolic = " P.++ show resV
                                                  ]
                              getModel
                    _ -> error $ "Unexpected output: " P.++ show cs


{-# ANN module ("HLint: ignore Use map once"   :: String) #-}
{-# ANN module ("HLint: ignore Use sum"        :: String) #-}
{-# ANN module ("HLint: ignore Fuse foldr/map" :: String) #-}
{-# ANN module ("HLint: ignore Use zipWith"    :: String) #-}
{-# ANN module ("HLint: ignore Use uncurry"    :: String) #-}
{-# ANN module ("HLint: ignore Use even"       :: String) #-}
{-# ANN module ("HLint: ignore Use odd"        :: String) #-}
{-# ANN module ("HLint: ignore Use product"    :: String) #-}
{-# ANN module ("HLint: ignore Avoid lambda"   :: String) #-}
