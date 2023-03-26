-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Quantifiers
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various combinations of quantifiers
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Quantifiers(tests) where

import Control.Monad (void)

import Utils.SBVTestFramework

data Q = E  -- exists
       | A  -- all

instance Show Q where
   show E = "exists"
   show A = "forall"

tests :: TestTree
tests = testGroup "Basics.Quantifiers" $ concatMap mkGoal goals ++ concatMap mkPred preds ++ others
   where mkGoal (g, nm) = [ goldenCapturedIO ("quantified_sat"   ++ "_" ++ nm) $ \rf -> void $ satWith   z3{verbose=True, redirectVerbose=Just rf} g
                          , goldenCapturedIO ("quantified_prove" ++ "_" ++ nm) $ \rf -> void $ proveWith z3{verbose=True, redirectVerbose=Just rf} g
                          ]
         mkPred (p, nm) = [ goldenCapturedIO ("quantified_sat"   ++ "_" ++ nm) $ \rf -> void $ satWith   z3{verbose=True, redirectVerbose=Just rf} p
                          , goldenCapturedIO ("quantified_prove" ++ "_" ++ nm) $ \rf -> void $ proveWith z3{verbose=True, redirectVerbose=Just rf} p
                          ]

         others = [ goldenCapturedIO "quantifiedB_0" $ check $ \(ExistsN @4 xs)   -> sAll (.< (20 :: SWord8)) xs .&& sum (1 : xs) .== (0::SWord8)
                  , goldenCapturedIO "quantifiedB_1" $ check $ \(ExistsN @4 xs)   -> sum xs .== (0::SWord8)
                  , goldenCapturedIO "quantifiedB_2" $ check $ \(ForallN @4 xs) k -> sum xs .== (k::SWord8)
                  ]
           where check p rf = do res <- satWith z3{verbose=True, redirectVerbose=Just rf} p
                                 appendFile rf $ "\nRESULT: "  ++ show res

         qs   = [E, A]

         acts = [ (\x y -> x + (y - x) .== y  , "thm")
                , (\x y -> x .== y .&& x ./= y, "contradiction")
                , (\x y -> x .== y + 1        , "satisfiable")
                ]

         goals = [(t1 q1 q2 a, show q1 ++ show q2 ++ "_" ++ an ++ "_c") | q1      <- qs
                                                                        , q2      <- qs
                                                                        , (a, an) <- acts
                                                                        ]

         preds = [(t2 q1 q2 a, show q1 ++ show q2 ++ "_" ++ an ++ "_p") | q1       <- qs
                                                                        , q2       <- qs
                                                                        , (a, an)  <- acts
                                                                        ]

         t1 :: Q -> Q -> (SWord8 -> SWord8 -> SBool) -> Goal
         t1 E E act = constrain $ \(Exists x) (Exists y) -> act x y
         t1 E A act = constrain $ \(Exists x) (Forall y) -> act x y
         t1 A E act = constrain $ \(Forall x) (Exists y) -> act x y
         t1 A A act = constrain $ \(Forall x) (Forall y) -> act x y

         t2 :: Q -> Q -> (SWord8 -> SWord8 -> SBool) -> Predicate
         t2 E E act = pure $ quantifiedBool $ \(Exists x) (Exists y) -> act x y
         t2 E A act = pure $ quantifiedBool $ \(Exists x) (Forall y) -> act x y
         t2 A E act = pure $ quantifiedBool $ \(Forall x) (Exists y) -> act x y
         t2 A A act = pure $ quantifiedBool $ \(Forall x) (Forall y) -> act x y

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
