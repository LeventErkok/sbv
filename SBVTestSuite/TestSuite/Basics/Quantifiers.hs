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

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

#if MIN_VERSION_base(4,19,0)
{-# LANGUAGE TypeAbstractions    #-}
#endif

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
                          ]
         mkPred (p, nm) = [ goldenCapturedIO ("quantified_sat"   ++ "_" ++ nm) $ \rf -> void $ satWith   z3{verbose=True, redirectVerbose=Just rf} p
                          , goldenCapturedIO ("quantified_prove" ++ "_" ++ nm) $ \rf -> void $ proveWith z3{verbose=True, redirectVerbose=Just rf} p
                          ]

         others = [ goldenCapturedIO "quantifiedB_0" $ check $ \(ExistsN @4 xs)   -> sAll (.< (20 :: SWord8)) xs .&& sum (1 : xs) .== (0::SWord8)
                  , goldenCapturedIO "quantifiedB_1" $ check $ \(ExistsN @4 xs)   -> sum xs .== (0::SWord8)
                  , goldenCapturedIO "quantifiedB_2" $ check $ \k (ForallN @4 xs) -> sum xs .== (k::SWord8)
                  , goldenCapturedIO "quantifiedB_3" $ check $ \k (ExistsN @4 xs) -> sum xs .== (k::SWord8)
                  , goldenCapturedIO "quantifiedB_4" $ check $ \(ExistsN @4 xs) (Exists k) -> sum xs .== (k::SWord8)
                  , goldenCapturedIO "quantifiedB_5" $ check $ \(ExistsN @4 xs) (Forall k) -> sum xs .== (k::SWord8)
                  , goldenCapturedIO "quantifiedB_6" $ check $ quantifiedBool (quantifiedBool (\(Exists (x::SBool)) -> x) )
                  , goldenCapturedIO "quantifiedB_7" $ check $ \(Exists (x :: SBool)) -> quantifiedBool (quantifiedBool (\(Exists (y::SBool)) -> x .|| y) )
                  , goldenCapturedIO "quantifiedB_8" $ check $ \(Exists (x :: SBool)) -> quantifiedBool (\(Exists (y::SBool)) -> x .|| y)
                  , goldenCapturedIO "quantifiedB_9" $ check $ quantifiedBool $ \(Exists (x :: SBool)) -> quantifiedBool (\(Exists (y::SBool)) -> x .|| y)
                  , goldenCapturedIO "quantifiedB_A" $ check $ \(Exists a) (Forall b) (Exists c) (Forall d) ->  a + b + c + d .== (0::SInteger)
                  , goldenCapturedIO "quantifiedB_B" $ check $ \(Forall a) (Exists b) (Forall c) (Exists d) ->  a + b + c + d .== (0::SInteger)
                  ]
           where check p rf = do res <- satWith z3{verbose=True, redirectVerbose=Just rf} p
                                 appendFile rf $ "\nRESULT: "  ++ show res ++ "\n"

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

         t1 :: Q -> Q -> (SWord8 -> SWord8 -> SBool) -> ConstraintSet
         t1 E E act = constrain $ \(Exists x) (Exists y) -> act x y
         t1 E A act = constrain $ \(Exists x) (Forall y) -> act x y
         t1 A E act = constrain $ \(Forall x) (Exists y) -> act x y
         t1 A A act = constrain $ \(Forall x) (Forall y) -> act x y

         t2 :: Q -> Q -> (SWord8 -> SWord8 -> SBool) -> Predicate
         t2 E E act = pure $ quantifiedBool $ \(Exists x) (Exists y) -> act x y
         t2 E A act = pure $ quantifiedBool $ \(Exists x) (Forall y) -> act x y
         t2 A E act = pure $ quantifiedBool $ \(Forall x) (Exists y) -> act x y
         t2 A A act = pure $ quantifiedBool $ \(Forall x) (Forall y) -> act x y

{- HLint ignore module "Reduce duplication"     -}
{- HLint ignore module "Unused LANGUAGE pragma" -}
