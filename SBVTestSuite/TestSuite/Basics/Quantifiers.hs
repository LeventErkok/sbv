-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Quantifiers
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various combinations of quantifiers
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

module TestSuite.Basics.Quantifiers(tests) where

import Control.Monad (void)

import Utils.SBVTestFramework

tests :: TestTree
tests = testGroup "Basics.Quantifiers" $ concatMap mkGoal goals ++ concatMap mkPred preds
   where mkGoal (g, nm) = [ goldenCapturedIO ("quantified_sat"   ++ "_" ++ nm) $ \rf -> void $ satWith   z3{verbose=True, redirectVerbose=Just rf} g
                          , goldenCapturedIO ("quantified_prove" ++ "_" ++ nm) $ \rf -> void $ proveWith z3{verbose=True, redirectVerbose=Just rf} g
                          ]
         mkPred (p, nm) = [ goldenCapturedIO ("quantified_sat"   ++ "_" ++ nm) $ \rf -> void $ satWith   z3{verbose=True, redirectVerbose=Just rf} p
                          , goldenCapturedIO ("quantified_prove" ++ "_" ++ nm) $ \rf -> void $ proveWith z3{verbose=True, redirectVerbose=Just rf} p
                          ]

         qs   = [(exists, "exists"), (forall, "forall")]

         acts = [ (\x y -> x + (y - x) .== y  , "thm")
                , (\x y -> x .== y .&& x ./= y, "contradiction")
                , (\x y -> x .== y + 1        , "satisfiable")
                ]

         goals = [(t1 q1 q2 a, nq1 ++ nq2 ++ "_" ++ an ++ "_c") | (q1, nq1) <- qs
                                                                , (q2, nq2) <- qs
                                                                , (a,  an)  <- acts ]

         preds = [(t2 q1 q2 a, nq1 ++ nq2 ++ "_" ++ an ++ "_p") | (q1, nq1) <- qs
                                                                , (q2, nq2) <- qs
                                                                , (a,  an)  <- acts ]

         t1 :: (String -> Symbolic SWord8) -> (String -> Symbolic SWord8) -> (SWord8 -> SWord8 -> SBool) -> Goal
         t1 q1 q2 act = q1 "x" >>= \x -> q2 "y" >>= \y -> constrain $ act x y

         t2 :: (String -> Symbolic SWord8) -> (String -> Symbolic SWord8) -> (SWord8 -> SWord8 -> SBool) -> Predicate
         t2 q1 q2 act = q1 "x" >>= \x -> q2 "y" >>= \y -> return    $ act x y
