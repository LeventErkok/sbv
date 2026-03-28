-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.TPCaching
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Tests for the TP proof caching mechanism.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.TPCaching(tests) where

import Utils.SBVTestFramework

import Data.SBV.TP (runTPWith, lemma, calc, recall, tpStats, (|-), (=:), qed)

import Control.Monad (void)

import Data.Char (isSpace)
import Data.List (isPrefixOf, dropWhileEnd)

import Control.DeepSeq (($!!))

-- | Strip timing info [0.05s] from the end of output lines.
stripTiming :: String -> String
stripTiming s
  | (_, rest@('[':_)) <- break (== '[') (dropWhileEnd isSpace s)
  , last rest == ']'
  = dropWhileEnd isSpace $ take (length s - length rest) s
  | True
  = s

-- | Filter out the statistics summary line from verbose output.
isStatsLine :: String -> Bool
isStatsLine s = "[SBV:" `isPrefixOf` dropWhile isSpace s

-- | Clean captured verbose output: strip timing and stats.
cleanStatsOutput :: String -> String
cleanStatsOutput = unlines . map stripTiming . filter (not . isStatsLine) . lines

-- Test suite
tests :: TestTree
tests = testGroup "Basics.TPCaching"
   [
   -- Normal mode: recall when cache is empty (cache miss).
   -- The proof runs from scratch; recallWith shows "Lemma:" one-liner.
     goldenCapturedIO "tpCache_miss" $ \rf -> do
        let cfg = z3 { redirectVerbose = Just rf }
        void $ runTPWith cfg $
           recall (lemma "fact" sTrue [])

   -- Normal mode: direct proof then recall (cache hit).
   -- The direct proof shows "Lemma:", the recall shows "Cached:".
   , goldenCapturedIO "tpCache_hit" $ \rf -> do
        let cfg = z3 { redirectVerbose = Just rf }
        void $ runTPWith cfg $ do
           _ <- lemma "fact" sTrue []
           recall (lemma "fact" sTrue [])

   -- Normal mode: same proposition proved under two names, then recalled (aliases).
   -- The recall shows "Cached:" with "(a.k.a. ...)" listing the other name.
   , goldenCapturedIO "tpCache_alias" $ \rf -> do
        let cfg = z3 { redirectVerbose = Just rf }
        void $ runTPWith cfg $ do
           _ <- lemma "nameA" sTrue []
           _ <- lemma "nameB" sTrue []
           recall (lemma "nameC" sTrue [])

   -- Normal mode: calc proof with steps, then recall (cache hit).
   -- The direct proof shows each step; the recall collapses to one line.
   , goldenCapturedIO "tpCache_calcCollapse" $ \rf -> do
        let cfg = z3 { redirectVerbose = Just rf }
        void $ runTPWith cfg $ do
           let addZeroProof = calc "addZero"
                                   (\(Forall @"x" (x :: SInteger)) -> x + 0 .== x) $
                                   \x -> [] |- x + 0
                                            =: (x :: SInteger)
                                            =: qed
           _ <- addZeroProof
           recall addZeroProof

   -- Normal mode: nested recall.
   -- First run proves inner and outer. Second run (via recall) hits cache for outer.
   , goldenCapturedIO "tpCache_nested" $ \rf -> do
        let cfg = z3 { redirectVerbose = Just rf }
        void $ runTPWith cfg $ do
           let myProof = do _ <- recall (lemma "inner" sTrue [])
                            lemma "outer" sTrue []
           _ <- myProof
           recall myProof

   -- Stats mode: recall when cache is empty (cache miss).
   -- In stats mode, recall does NOT suppress inner output, so full proof steps are visible.
   , goldenCapturedIO "tpCache_statsMiss" $ \rf -> do
        let cfg = (tpStats z3) { redirectVerbose = Just rf }
        void $ runTPWith cfg $
           recall (calc "addZero"
                        (\(Forall @"x" (x :: SInteger)) -> x + 0 .== x) $
                        \x -> [] |- x + 0
                                 =: (x :: SInteger)
                                 =: qed)
        contents <- readFile rf
        writeFile rf $!! cleanStatsOutput contents

   -- Stats mode: direct proof then recall (cache hit).
   -- Direct proof shows full steps; recall shows "Cached:" one-liner.
   , goldenCapturedIO "tpCache_statsHit" $ \rf -> do
        let cfg = (tpStats z3) { redirectVerbose = Just rf }
        void $ runTPWith cfg $ do
           let addZeroProof = calc "addZero"
                                   (\(Forall @"x" (x :: SInteger)) -> x + 0 .== x) $
                                   \x -> [] |- x + 0
                                            =: (x :: SInteger)
                                            =: qed
           _ <- addZeroProof
           recall addZeroProof
        contents <- readFile rf
        writeFile rf $!! cleanStatsOutput contents

   -- Stats mode: nested recall showing inner cache dynamics.
   -- First recall misses (shows full inner proofs). Second recall hits (shows "Cached:").
   , goldenCapturedIO "tpCache_statsNested" $ \rf -> do
        let cfg = (tpStats z3) { redirectVerbose = Just rf }
        void $ runTPWith cfg $ do
           _ <- recall (lemma "inner" sTrue [])
           _ <- lemma "outer" sTrue []
           _ <- recall (lemma "inner" sTrue [])
           recall (lemma "outer" sTrue [])
        contents <- readFile rf
        writeFile rf $!! cleanStatsOutput contents
   ]
