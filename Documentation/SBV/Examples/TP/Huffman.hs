-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Huffman
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Optimality of Huffman coding for positive integer frequencies. 'huffman'
-- takes a nonempty, sorted frequency queue and constructs a full binary code
-- tree. 'correctness' proves that it preserves every frequency and has no
-- greater weighted path length than any other full binary tree with the same
-- frequencies. There is no bound on the queue length or tree size.
--
-- Trees carry weights rather than character labels: the cost depends only on
-- weights and depths, so repeated frequencies are tracked by multiplicities.
-- Symbols with equal frequencies can be assigned to the corresponding leaves
-- in any order. A singleton alphabet receives a zero-length code.
--
-- The proof follows the greedy argument. 'greedyChoice' places the two minimum
-- weights at sibling positions without increasing cost. 'contraction' replaces
-- them by their sum. Strong induction on the queue length compares the recursive
-- Huffman tree with this contracted competitor. All recursive definitions have
-- checked termination measures; the proof introduces no axioms.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP               #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeAbstractions  #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Huffman where

import Data.SBV
import Data.SBV.TP

import qualified Data.SBV.List as L

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Trees and weighted path length

-- | A full binary code tree. Leaves carry integer frequencies; internal
-- nodes represent a choice of the next bit. Optimality uses positive weights.
data Tree = Leaf Integer | Fork Tree Tree
          deriving (Eq, Show)

-- | A tree with one hole. Filling the hole selects an arbitrary subtree,
-- retaining both the siblings along its path and their left/right positions.
data Context = Hole | GoLeft Context Tree | GoRight Tree Context
             deriving (Eq, Show)

-- | A selected sibling pair, together with the context surrounding its fork.
data SiblingPair = SiblingPair Context Integer Integer
                 deriving (Eq, Show)

-- | Symbolic trees and contexts, with their structural induction principles.
mkSymbolic [''Tree, ''Context, ''SiblingPair]

-- | A deliberately unbalanced tree, with two occurrences of the minimum
-- weight. Moving them together illustrates why multiplicities matter.
--
-- >>> unliteral exampleTree
-- Just (Fork (Leaf 1) (Fork (Leaf 5) (Fork (Leaf 1) (Leaf 3))))
exampleTree :: STree
exampleTree = literal $ Fork (Leaf 1) (Fork (Leaf 5) (Fork (Leaf 1) (Leaf 3)))

-- | Sum of the leaf weights.
--
-- >>> weight exampleTree
-- 10 :: SInteger
weight :: STree -> SInteger
weight = smtFunction "weight" $ \t -> [sCase| t of
                                         Leaf w   -> w
                                         Fork l r -> weight l + weight r
                                      |]

-- | Weighted external path length. Each branch adds one bit to every code
-- below it; this recurrence avoids explicitly multiplying weights by depths.
--
-- >>> cost exampleTree
-- 23 :: SInteger
cost :: STree -> SInteger
cost = smtFunction "cost" $ \t -> [sCase| t of
                                     Leaf _   -> 0
                                     Fork l r -> cost l + cost r + weight l + weight r
                                  |]

-- | Number of leaves carrying a particular weight. Comparing this for every
-- weight expresses multiset equality, including repeated frequencies.
--
-- >>> count 1 exampleTree
-- 2 :: SInteger
count :: SInteger -> STree -> SInteger
count = smtFunction "count" $ \w t -> [sCase| t of
                                         Leaf v   -> ite (w .== v) 1 0
                                         Fork l r -> count w l + count w r
                                      |]

-- * Tree contexts and contraction

-- | Replace the hole with a tree.
--
-- >>> unliteral $ plug (literal (GoRight (Leaf 4) Hole)) (sLeaf 2)
-- Just (Fork (Leaf 4) (Leaf 2))
plug :: SContext -> STree -> STree
plug = smtFunction "plug" $ \c t -> [sCase| c of
                                       Hole        -> t
                                       GoLeft k r  -> sFork (plug k t) r
                                       GoRight l k -> sFork l (plug k t)
                                    |]

-- | Depth of the hole, measured from the root.
--
-- >>> depth $ literal $ GoRight (Leaf 4) Hole
-- 1 :: SInteger
depth :: SContext -> SInteger
depth = smtFunction "depth" $ \c -> [sCase| c of
                                       Hole        -> 0
                                       GoLeft k _  -> 1 + depth k
                                       GoRight _ k -> 1 + depth k
                                    |]

-- | Total weight outside the hole.
--
-- >>> outsideWeight $ pairContext $ deepestPair exampleTree
-- 6 :: SInteger
outsideWeight :: SContext -> SInteger
outsideWeight = smtFunction "outsideWeight" $ \c -> [sCase| c of
                                                       Hole        -> 0
                                                       GoLeft  k r -> outsideWeight k + weight r
                                                       GoRight l k -> weight l + outsideWeight k
                                                    |]

-- | Cost contributed by the context when the hole is a zero-weight leaf.
--
-- >>> outsideCost $ pairContext $ deepestPair exampleTree
-- 11 :: SInteger
outsideCost :: SContext -> SInteger
outsideCost = smtFunction "outsideCost" $ \c -> [sCase| c of
                                                   Hole        -> 0
                                                   GoLeft  k r -> outsideCost k + cost r + outsideWeight k + weight r
                                                   GoRight l k -> cost l + outsideCost k + weight l + outsideWeight k
                                                |]

-- | Multiplicity of a weight outside the hole.
--
-- >>> outsideCount 1 $ pairContext $ deepestPair exampleTree
-- 1 :: SInteger
outsideCount :: SInteger -> SContext -> SInteger
outsideCount = smtFunction "outsideCount" $ \w c -> [sCase| c of
                                                       Hole        -> 0
                                                       GoLeft  k r -> outsideCount w k + count w r
                                                       GoRight l k -> count w l + outsideCount w k
                                                    |]

-- | Filling the hole adds exactly the inserted tree's weight.
--
-- >>> runTP weightPlug
-- Lemma: weightPlug    Q.E.D.
-- Functions proven terminating: outsideWeight, plug, weight
-- [Proven] weightPlug :: Ɐc ∷ Context → Ɐt ∷ Tree → Bool
weightPlug :: TP (Proof (Forall "c" Context -> Forall "t" Tree -> SBool))
weightPlug = inductiveLemma "weightPlug" (\(Forall c) (Forall t) -> weight (plug c t) .== outsideWeight c + weight t) []

-- | Filling the hole preserves the multiplicities outside it.
--
-- >>> runTP countPlug
-- Lemma: countPlug    Q.E.D.
-- Functions proven terminating: count, outsideCount, plug
-- [Proven] countPlug :: Ɐc ∷ Context → Ɐt ∷ Tree → Ɐw ∷ Integer → Bool
countPlug :: TP (Proof (Forall "c" Context -> Forall "t" Tree -> Forall "w" Integer -> SBool))
countPlug = inductiveLemma "countPlug" (\(Forall c) (Forall t) (Forall w) -> count w (plug c t) .== outsideCount w c + count w t) []

-- | The inserted tree keeps its internal cost; every leaf also acquires
-- 'depth' additional bits from the surrounding context.
--
-- >>> runTP costPlug
-- Lemma: weightPlug                     Q.E.D.
-- Lemma: depthNonNegative               Q.E.D.
-- Inductive lemma (strong): costPlug
--   Step: Measure is non-negative       Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                         Q.E.D.
--     Step: 1.2.1                       Q.E.D.
--     Step: 1.2.2                       Q.E.D.
--     Step: 1.2.3                       Q.E.D.
--     Step: 1.2.4                       Q.E.D.
--     Step: 1.2.5                       Q.E.D.
--     Step: 1.3.1                       Q.E.D.
--     Step: 1.3.2                       Q.E.D.
--     Step: 1.3.3                       Q.E.D.
--     Step: 1.3.4                       Q.E.D.
--     Step: 1.3.5                       Q.E.D.
--     Step: 1.Completeness              Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating: cost, depth, outsideCost, outsideWeight, plug, weight
-- [Proven] costPlug :: Ɐc ∷ Context → Ɐt ∷ Tree → Bool
costPlug :: TP (Proof (Forall "c" Context -> Forall "t" Tree -> SBool))
costPlug = do
  wp <- recall weightPlug
  dp <- recall depthNonNegative
  sInduct "costPlug"
    (\(Forall c) (Forall t) -> cost (plug c t) .== outsideCost c + cost t + depth c * weight t)
    (\c _ -> depth c, [proofOf dp]) $ \ih c t ->
      [] |- cost (plug c t)
         =: [pCase| c of
               Hole        -> cost t =: qed
               GoLeft k r  -> cost (plug (sGoLeft k r) t)
                           =: cost (plug k t) + cost r + weight (plug k t) + weight r
                           ?? ih `at` (Inst @"c" k, Inst @"t" t)
                           =: outsideCost k + cost t + depth k * weight t + cost r + weight (plug k t) + weight r
                           ?? wp `at` (Inst @"c" k, Inst @"t" t)
                           =: outsideCost k + cost t + depth k * weight t + cost r + outsideWeight k + weight t + weight r
                           =: outsideCost (sGoLeft k r) + cost t + depth (sGoLeft k r) * weight t
                           =: qed
               GoRight l k -> cost (plug (sGoRight l k) t)
                           =: cost l + cost (plug k t) + weight l + weight (plug k t)
                           ?? ih `at` (Inst @"c" k, Inst @"t" t)
                           =: cost l + outsideCost k + cost t + depth k * weight t + weight l + weight (plug k t)
                           ?? wp `at` (Inst @"c" k, Inst @"t" t)
                           =: cost l + outsideCost k + cost t + depth k * weight t + weight l + outsideWeight k + weight t
                           =: outsideCost (sGoRight l k) + cost t + depth (sGoRight l k) * weight t
                           =: qed
            |]

-- | Context depth is a nonnegative induction measure.
--
-- >>> runTP depthNonNegative
-- Lemma: depthNonNegative    Q.E.D.
-- Functions proven terminating: depth
-- [Proven] depthNonNegative :: Ɐc ∷ Context → Bool
depthNonNegative :: TP (Proof (Forall "c" Context -> SBool))
depthNonNegative = inductiveLemma "depthNonNegative" (\(Forall c) -> depth c .>= 0) []

-- | Contracting sibling leaves of weights @a@ and @b@ to a single leaf of
-- weight @a+b@ decreases the total cost by exactly @a+b@, at any depth.
--
-- >>> runTP contraction
-- Lemma: costPlug                       Q.E.D.
-- Lemma: contraction
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating: cost, depth, outsideCost, outsideWeight, plug, weight
-- [Proven] contraction :: Ɐc ∷ Context → Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
contraction :: TP (Proof (Forall "c" Context -> Forall "a" Integer -> Forall "b" Integer -> SBool))
contraction = do
  cp <- recall costPlug
  calc "contraction"
       (\(Forall c) (Forall a) (Forall b) -> cost (plug c (sFork (sLeaf a) (sLeaf b))) .== cost (plug c (sLeaf (a+b))) + a+b) $ \c a b ->
       [] |- cost (plug c (sFork (sLeaf a) (sLeaf b)))
          ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf a) (sLeaf b)))
          =: outsideCost c + a+b + depth c * (a+b)
          ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf (a+b)))
          =: cost (plug c (sLeaf (a+b))) + a+b
          =: qed

-- * Finding deepest siblings

-- | Maximum leaf depth. A tree consisting of one leaf has height zero.
--
-- >>> height exampleTree
-- 3 :: SInteger
height :: STree -> SInteger
height = smtFunction "height" $ \t -> [sCase| t of
                                         Leaf _   -> 0
                                         Fork l r -> 1 + smax (height l) (height r)
                                      |]

-- | Select a deepest sibling pair, preferring the left subtree on ties.
-- The singleton case is a placeholder; 'deepestPairCorrect' requires a fork.
--
-- >>> unliteral $ deepestPair exampleTree
-- Just (SiblingPair (GoRight (Leaf 1) (GoRight (Leaf 5) Hole)) 1 3)
deepestPair :: STree -> SSiblingPair
deepestPair = smtFunction "deepestPair" $ \t -> [sCase| t of
                                                   Leaf w                           -> sSiblingPair sHole w w
                                                   Fork (Leaf a) (Leaf b)           -> sSiblingPair sHole a b
                                                   Fork l r | height l .>= height r -> case deepestPair l of
                                                                                         SiblingPair c a b -> sSiblingPair (sGoLeft c r) a b
                                                            | True                  -> case deepestPair r of
                                                                                         SiblingPair c a b -> sSiblingPair (sGoRight l c) a b
                                                |]

-- | Reconstruct a tree from a selected sibling pair and its context.
--
-- >>> rebuildPair (deepestPair exampleTree) .== exampleTree
-- True
rebuildPair :: SSiblingPair -> STree
rebuildPair p = [sCase| p of
                   SiblingPair c a b -> plug c (sFork (sLeaf a) (sLeaf b))
                |]

-- | Depth of either selected sibling leaf.
--
-- >>> siblingDepth $ deepestPair exampleTree
-- 3 :: SInteger
siblingDepth :: SSiblingPair -> SInteger
siblingDepth p = [sCase| p of
                    SiblingPair c _ _ -> depth c + 1
                 |]

-- | Every tree has a nonnegative height.
--
-- >>> runTP heightNonNegative
-- Lemma: heightNonNegative    Q.E.D.
-- Functions proven terminating: height
-- [Proven] heightNonNegative :: Ɐt ∷ Tree → Bool
heightNonNegative :: TP (Proof (Forall "t" Tree -> SBool))
heightNonNegative = inductiveLemma "heightNonNegative" (\(Forall t) -> height t .>= 0) []

-- | Height zero characterizes leaves; every fork has positive height.
--
-- >>> runTP heightZero
-- Lemma: heightNonNegative    Q.E.D.
-- Lemma: heightZero           Q.E.D.
-- Functions proven terminating: height
-- [Proven] heightZero :: Ɐt ∷ Tree → Bool
heightZero :: TP (Proof (Forall "t" Tree -> SBool))
heightZero = do
  hn <- recall heightNonNegative
  lemma "heightZero" (\(Forall t) -> (height t .== 0) .== isLeaf t) [proofOf hn]

-- | Selecting deepest siblings preserves the entire original tree, and both
-- selected leaves are at its maximum depth. Thus the selection is structural,
-- not an assumption about an already suitably arranged tree.
--
-- >>> runTP deepestPairCorrect
-- Lemma: heightNonNegative     Q.E.D.
-- Lemma: heightZero            Q.E.D.
-- Lemma: deepestPairCorrect    Q.E.D.
-- Functions proven terminating: deepestPair, depth, height, plug
-- [Proven] deepestPairCorrect :: Ɐt ∷ Tree → Bool
deepestPairCorrect :: TP (Proof (Forall "t" Tree -> SBool))
deepestPairCorrect = do
  hn <- recall heightNonNegative
  hz <- recall heightZero
  inductiveLemma "deepestPairCorrect"
                 (\(Forall t) -> isFork t .=> rebuildPair (deepestPair t) .== t .&& siblingDepth (deepestPair t) .== height t)
                 [proofOf hn, proofOf hz]

-- * Locating and replacing leaves

-- | Replace the first occurrence of a leaf weight, searching left before
-- right. If the weight is absent, the tree is unchanged.
--
-- >>> unliteral $ replace 1 2 exampleTree
-- Just (Fork (Leaf 2) (Fork (Leaf 5) (Fork (Leaf 1) (Leaf 3))))
--
-- >>> replace 99 2 exampleTree .== exampleTree
-- True
replace :: SInteger -> SInteger -> STree -> STree
replace = smtFunction "replace" $ \old new t -> [sCase| t of
                                                   Leaf w   -> sLeaf (ite (w .== old) new w)
                                                   Fork l r | count old l .> 0 -> sFork (replace old new l) r
                                                            | True            -> sFork l (replace old new r)
                                                |]

-- | Depth of the first leaf with the given weight, using the same traversal
-- as 'replace'. When absent this returns the rightmost leaf's depth.
--
-- >>> leafDepth 1 exampleTree
-- 1 :: SInteger
leafDepth :: SInteger -> STree -> SInteger
leafDepth = smtFunction "leafDepth" $ \w t -> [sCase| t of
                                                 Leaf _   -> 0
                                                 Fork l r -> 1 + ite (count w l .> 0) (leafDepth w l) (leafDepth w r)
                                              |]

-- | Leaf multiplicities are nonnegative.
--
-- >>> runTP countNonNegative
-- Lemma: countNonNegative    Q.E.D.
-- Functions proven terminating: count
-- [Proven] countNonNegative :: Ɐt ∷ Tree → Ɐw ∷ Integer → Bool
countNonNegative :: TP (Proof (Forall "t" Tree -> Forall "w" Integer -> SBool))
countNonNegative = inductiveLemma "countNonNegative" (\(Forall t) (Forall w) -> count w t .>= 0) []

-- | Replacing a weight preserves the shape and hence the height of the tree.
--
-- >>> runTP replaceHeight
-- Lemma: replaceHeight    Q.E.D.
-- Functions proven terminating: count, height, replace
-- [Proven] replaceHeight :: Ɐt ∷ Tree → Ɐold ∷ Integer → Ɐnew ∷ Integer → Bool
replaceHeight :: TP (Proof (Forall "t" Tree -> Forall "old" Integer -> Forall "new" Integer -> SBool))
replaceHeight = inductiveLemma "replaceHeight" (\(Forall t) (Forall old) (Forall new) -> height (replace old new t) .== height t) []

-- | The replacement changes exactly one occurrence, even when weights tie.
--
-- >>> runTP replaceCount
-- Lemma: countNonNegative    Q.E.D.
-- Lemma: replaceCount        Q.E.D.
-- Functions proven terminating: count, replace
-- [Proven] replaceCount :: Ɐt ∷ Tree → Ɐold ∷ Integer → Ɐnew ∷ Integer → Ɐw ∷ Integer → Bool
replaceCount :: TP (Proof (Forall "t" Tree -> Forall "old" Integer -> Forall "new" Integer -> Forall "w" Integer -> SBool))
replaceCount = do
  cn <- recall countNonNegative
  inductiveLemma "replaceCount"
    (\(Forall t) (Forall old) (Forall new) (Forall w) -> count old t .> 0 .=>
       count w (replace old new t) .== count w t + ite (w .== new) 1 0 - ite (w .== old) 1 0)
    [proofOf cn]

-- | Exact cost of replacing a selected leaf, at its actual depth.
--
-- >>> runTP replaceCost
-- Lemma: locateCorrect                  Q.E.D.
-- Lemma: costPlug                       Q.E.D.
-- Lemma: replaceCost
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Step: 3                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating: cost, count, depth, leafDepth, locate, outsideCost, outsideWeight, plug, replace, weight
-- [Proven] replaceCost :: Ɐt ∷ Tree → Ɐold ∷ Integer → Ɐnew ∷ Integer → Bool
replaceCost :: TP (Proof (Forall "t" Tree -> Forall "old" Integer -> Forall "new" Integer -> SBool))
replaceCost = do
  lc <- recall locateCorrect
  cp <- recall costPlug
  calc "replaceCost"
    (\(Forall t) (Forall old) (Forall new) -> count old t .> 0 .=>
       cost (replace old new t) .== cost t + (new-old) * leafDepth old t) $ \t old new ->
      let c = locate old t
      in [count old t .> 0]
         |- cost (replace old new t)
         ?? lc `at` (Inst @"t" t, Inst @"w" old, Inst @"new" new)
         =: cost (plug c (sLeaf new))
         ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf new))
         =: outsideCost c + depth c * new
         ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf old))
         ?? lc `at` (Inst @"t" t, Inst @"w" old, Inst @"new" new)
         =: cost t + (new-old) * leafDepth old t
         =: qed

-- | Locate the first occurrence of a weight as a context. The result is
-- meaningful when the weight occurs in the tree.
--
-- >>> unliteral $ locate 5 exampleTree
-- Just (GoRight (Leaf 1) (GoLeft Hole (Fork (Leaf 1) (Leaf 3))))
locate :: SInteger -> STree -> SContext
locate = smtFunction "locate" $ \w t -> [sCase| t of
                                           Leaf _   -> sHole
                                           Fork l r | count w l .> 0 -> sGoLeft (locate w l) r
                                                    | True          -> sGoRight l (locate w r)
                                        |]

-- | The selected context reconstructs the tree, implements replacement,
-- and records the same leaf depth as the direct traversal.
--
-- >>> runTP locateCorrect
-- Lemma: countNonNegative    Q.E.D.
-- Lemma: locateCorrect       Q.E.D.
-- Functions proven terminating: count, depth, leafDepth, locate, plug, replace
-- [Proven] locateCorrect :: Ɐt ∷ Tree → Ɐw ∷ Integer → Ɐnew ∷ Integer → Bool
locateCorrect :: TP (Proof (Forall "t" Tree -> Forall "w" Integer -> Forall "new" Integer -> SBool))
locateCorrect = do
  cn <- recall countNonNegative
  inductiveLemma "locateCorrect"
    (\(Forall t) (Forall w) (Forall new) -> count w t .> 0 .=>
       plug (locate w t) (sLeaf w) .== t
       .&& plug (locate w t) (sLeaf new) .== replace w new t
       .&& depth (locate w t) .== leafDepth w t)
    [proofOf cn]

-- | The selected leaf is no deeper than the deepest leaf.
--
-- >>> runTP leafDepthBound
-- Lemma: leafDepthBound    Q.E.D.
-- Functions proven terminating: count, height, leafDepth
-- [Proven] leafDepthBound :: Ɐt ∷ Tree → Ɐw ∷ Integer → Bool
leafDepthBound :: TP (Proof (Forall "t" Tree -> Forall "w" Integer -> SBool))
leafDepthBound = inductiveLemma "leafDepthBound" (\(Forall t) (Forall w) -> leafDepth w t .<= height t) []

-- * Replacing leaves outside a context

-- | Replace the first occurrence outside the hole, leaving the hole itself
-- untouched. This lets us install a minimum weight in a chosen sibling pair
-- without disturbing the other member of that pair.
--
-- >>> unliteral $ replaceOutside 1 3 $ pairContext $ deepestPair exampleTree
-- Just (GoRight (Leaf 3) (GoRight (Leaf 5) Hole))
replaceOutside :: SInteger -> SInteger -> SContext -> SContext
replaceOutside = smtFunction "replaceOutside" $ \old new c ->
  [sCase| c of
     Hole                                  -> sHole

     GoLeft k r  | outsideCount old k .> 0 -> sGoLeft (replaceOutside old new k) r
                 | True                    -> sGoLeft k (replace old new r)

     GoRight l k | count old l .> 0        -> sGoRight (replace old new l) k
                 | True                    -> sGoRight l (replaceOutside old new k)
  |]

-- | Replacing outside leaves does not change the hole's depth.
--
-- >>> runTP replaceOutsideDepth
-- Lemma: replaceOutsideDepth    Q.E.D.
-- Functions proven terminating: count, depth, outsideCount, replace, replaceOutside
-- [Proven] replaceOutsideDepth :: Ɐc ∷ Context → Ɐold ∷ Integer → Ɐnew ∷ Integer → Bool
replaceOutsideDepth :: TP (Proof (Forall "c" Context -> Forall "old" Integer -> Forall "new" Integer -> SBool))
replaceOutsideDepth = inductiveLemma "replaceOutsideDepth" (\(Forall c) (Forall old) (Forall new) -> depth (replaceOutside old new c) .== depth c) []

-- | A zero-weight leaf marks the hole. Replacing a nonzero weight in that
-- tree is exactly replacement outside the context's hole.
--
-- >>> runTP replaceOutsideEmbedding
-- Lemma: countPlug                  Q.E.D.
-- Lemma: replaceOutsideEmbedding    Q.E.D.
-- Functions proven terminating: count, outsideCount, plug, replace, replaceOutside
-- [Proven] replaceOutsideEmbedding :: Ɐc ∷ Context → Ɐold ∷ Integer → Ɐnew ∷ Integer → Bool
replaceOutsideEmbedding :: TP (Proof (Forall "c" Context -> Forall "old" Integer -> Forall "new" Integer -> SBool))
replaceOutsideEmbedding = do
  cp <- recall countPlug

  inductiveLemma "replaceOutsideEmbedding"
    (\(Forall c) (Forall old) (Forall new) -> old ./= 0 .=>
       plug (replaceOutside old new c) (sLeaf 0) .== replace old new (plug c (sLeaf 0)))
    [proofOf cp]

-- | Multiplicity change outside the hole, derived from replacement in the
-- tree marked with a zero-weight leaf.
--
-- >>> runTP replaceOutsideCount
-- Lemma: replaceOutsideEmbedding    Q.E.D.
-- Lemma: replaceCount               Q.E.D.
-- Lemma: countPlug                  Q.E.D. [Cached]
-- Lemma: replaceOutsideCount
--   Step: 1                         Q.E.D.
--   Step: 2                         Q.E.D.
--   Step: 3                         Q.E.D.
--   Step: 4                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: count, outsideCount, plug, replace, replaceOutside
-- [Proven] replaceOutsideCount :: Ɐc ∷ Context → Ɐold ∷ Integer → Ɐnew ∷ Integer → Ɐw ∷ Integer → Bool
replaceOutsideCount :: TP (Proof (Forall "c" Context -> Forall "old" Integer -> Forall "new" Integer -> Forall "w" Integer -> SBool))
replaceOutsideCount = do
  re <- recall replaceOutsideEmbedding
  rc <- recall replaceCount
  cp <- recall countPlug

  calc "replaceOutsideCount"
    (\(Forall c) (Forall old) (Forall new) (Forall w) -> old ./= 0 .&& outsideCount old c .> 0 .=>
       outsideCount w (replaceOutside old new c) .== outsideCount w c + ite (w .== new) 1 0 - ite (w .== old) 1 0) $ \c old new w ->
      let changed = replaceOutside old new c
          marked = plug c (sLeaf 0)
      in [old ./= 0, outsideCount old c .> 0]
      |- outsideCount w changed
      ?? cp `at` (Inst @"c" changed, Inst @"t" (sLeaf 0), Inst @"w" w)
      =: count w (plug changed (sLeaf 0)) - ite (w .== 0) 1 0
      ?? re `at` (Inst @"c" c, Inst @"old" old, Inst @"new" new)
      =: count w (replace old new marked) - ite (w .== 0) 1 0
      ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf 0), Inst @"w" old)
      ?? rc `at` (Inst @"t" marked, Inst @"old" old, Inst @"new" new, Inst @"w" w)
      =: count w marked + ite (w .== new) 1 0 - ite (w .== old) 1 0 - ite (w .== 0) 1 0
      ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf 0), Inst @"w" w)
      =: outsideCount w c + ite (w .== new) 1 0 - ite (w .== old) 1 0
      =: qed

-- | Replacing weights outside the hole preserves the marked tree's height.
--
-- >>> runTP replaceOutsideHeight
-- Lemma: replaceOutsideEmbedding    Q.E.D.
-- Lemma: replaceHeight              Q.E.D.
-- Lemma: replaceOutsideHeight
--   Step: 1                         Q.E.D.
--   Step: 2                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: count, height, outsideCount, plug, replace, replaceOutside
-- [Proven] replaceOutsideHeight :: Ɐc ∷ Context → Ɐold ∷ Integer → Ɐnew ∷ Integer → Bool
replaceOutsideHeight :: TP (Proof (Forall "c" Context -> Forall "old" Integer -> Forall "new" Integer -> SBool))
replaceOutsideHeight = do
  re <- recall replaceOutsideEmbedding
  rh <- recall replaceHeight

  calc "replaceOutsideHeight"
    (\(Forall c) (Forall old) (Forall new) -> old ./= 0 .=>
       height (plug (replaceOutside old new c) (sLeaf 0)) .== height (plug c (sLeaf 0))) $ \c old new ->
      [old ./= 0] |- height (plug (replaceOutside old new c) (sLeaf 0))
                  ?? re `at` (Inst @"c" c, Inst @"old" old, Inst @"new" new)
                  =: height (replace old new (plug c (sLeaf 0)))
                  ?? rh `at` (Inst @"t" (plug c (sLeaf 0)), Inst @"old" old, Inst @"new" new)
                  =: height (plug c (sLeaf 0))
                  =: qed

-- | Exact change to the outside cost when one nonzero weight is replaced.
--
-- >>> runTP replaceOutsideCost
-- Lemma: replaceOutsideEmbedding        Q.E.D.
-- Lemma: replaceCost                    Q.E.D.
-- Lemma: costPlug                       Q.E.D. [Cached]
-- Lemma: countPlug                      Q.E.D. [Cached]
-- Lemma: replaceOutsideCost
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Step: 3                             Q.E.D.
--   Step: 4                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating:
--   cost, count, depth, leafDepth, locate, outsideCost, outsideCount, outsideWeight, plug,
--   replace, replaceOutside, weight
-- [Proven] replaceOutsideCost :: Ɐc ∷ Context → Ɐold ∷ Integer → Ɐnew ∷ Integer → Bool
replaceOutsideCost :: TP (Proof (Forall "c" Context -> Forall "old" Integer -> Forall "new" Integer -> SBool))
replaceOutsideCost = do
  re <- recall replaceOutsideEmbedding
  rc <- recall replaceCost
  cp <- recall costPlug
  cn <- recall countPlug

  calc "replaceOutsideCost"
    (\(Forall c) (Forall old) (Forall new) -> old ./= 0 .&& outsideCount old c .> 0 .=>
       outsideCost (replaceOutside old new c) .== outsideCost c + (new-old) * leafDepth old (plug c (sLeaf 0))) $ \c old new ->
      let changed = replaceOutside old new c
          marked = plug c (sLeaf 0)
      in [old ./= 0, outsideCount old c .> 0]
      |- outsideCost changed
      ?? cp `at` (Inst @"c" changed, Inst @"t" (sLeaf 0))
      =: cost (plug changed (sLeaf 0))
      ?? re `at` (Inst @"c" c, Inst @"old" old, Inst @"new" new)
      =: cost (replace old new marked)
      ?? cn `at` (Inst @"c" c, Inst @"t" (sLeaf 0), Inst @"w" old)
      ?? rc `at` (Inst @"t" marked, Inst @"old" old, Inst @"new" new)
      =: cost marked + (new-old) * leafDepth old marked
      ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf 0))
      =: outsideCost c + (new-old) * leafDepth old marked
      =: qed

-- * Moving minimum weights into sibling positions

-- | A smaller inserted tree cannot increase the height of its context.
--
-- >>> runTP heightPlugMonotone
-- Lemma: depthNonNegative                         Q.E.D.
-- Inductive lemma (strong): heightPlugMonotone
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.3.1                                 Q.E.D.
--     Step: 1.3.2                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: depth, height, plug
-- [Proven] heightPlugMonotone :: Ɐc ∷ Context → Ɐu ∷ Tree → Ɐv ∷ Tree → Bool
heightPlugMonotone :: TP (Proof (Forall "c" Context -> Forall "u" Tree -> Forall "v" Tree -> SBool))
heightPlugMonotone = do
  dn <- recall depthNonNegative
  sInduct "heightPlugMonotone"
    (\(Forall c) (Forall u) (Forall v) -> height u .<= height v .=> height (plug c u) .<= height (plug c v))
    (\c _ _ -> depth c, [proofOf dn]) $ \ih c u v ->
      [height u .<= height v] |- height (plug c u) .<= height (plug c v)
                              =: [pCase| c of
                                   Hole        -> height u .<= height v =: sTrue =: qed

                                   GoLeft k r  -> smax (height (plug k u)) (height r) .<= smax (height (plug k v)) (height r)
                                               ?? ih `at` (Inst @"c" k, Inst @"u" u, Inst @"v" v)
                                               =: sTrue
                                               =: qed

                                   GoRight l k -> smax (height l) (height (plug k u)) .<= smax (height l) (height (plug k v))
                                               ?? ih `at` (Inst @"c" k, Inst @"u" u, Inst @"v" v)
                                               =: sTrue
                                               =: qed
                                 |]

-- | Children inserted at the hole would be at least as deep as every outside
-- leaf, allowing them to receive smaller weights without increasing cost.
deepest :: SContext -> SBool
deepest c = height (plug c (sLeaf 0)) .<= depth c + 1

-- | The context selected by 'deepestPair' satisfies the depth bound needed
-- when moving minimum weights into the selected sibling positions.
--
-- >>> runTP deepestPairBound
-- Lemma: deepestPairCorrect                       Q.E.D.
-- Lemma: heightPlugMonotone                       Q.E.D.
-- Lemma: deepestPairBound
--   Step: 1                                       Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: deepestPair, depth, height, plug
-- [Proven] deepestPairBound :: Ɐt ∷ Tree → Bool
deepestPairBound :: TP (Proof (Forall "t" Tree -> SBool))
deepestPairBound = do
  dp <- recall deepestPairCorrect
  hm <- recall heightPlugMonotone

  calc "deepestPairBound"
    (\(Forall t) -> isFork t .=> deepest (pairContext (deepestPair t))) $ \t ->
      let p = deepestPair t
          c = pairContext p
          u = sLeaf 0
          v = sFork (sLeaf (firstWeight p)) (sLeaf (secondWeight p))
      in [isFork t] |- deepest c
                    ?? dp `at` Inst @"t" t
                    ?? hm `at` (Inst @"c" c, Inst @"u" u, Inst @"v" v)
                    =: sTrue
                    =: qed

-- | Exact cost at a selected sibling pair.
--
-- >>> runTP siblingCost
-- Lemma: costPlug                       Q.E.D.
-- Lemma: siblingCost                    Q.E.D.
-- Functions proven terminating: cost, depth, outsideCost, outsideWeight, plug, weight
-- [Proven] siblingCost :: Ɐc ∷ Context → Ɐx ∷ Integer → Ɐy ∷ Integer → Bool
siblingCost :: TP (Proof (Forall "c" Context -> Forall "x" Integer -> Forall "y" Integer -> SBool))
siblingCost = do
  cp <- recall costPlug
  lemma "siblingCost"
    (\(Forall c) (Forall x) (Forall y) ->
       cost (plug c (sFork (sLeaf x) (sLeaf y))) .== outsideCost c + (depth c + 1) * (x+y))
    [proofOf cp]

-- | Exchange an outside minimum with the left leaf of a deepest sibling
-- pair. The right leaf is untouched, so it can hold a previously placed
-- minimum even when the two smallest weights are equal.
--
-- >>> runTP sinkCost
-- Lemma: replaceOutsideCost             Q.E.D.
-- Lemma: replaceOutsideDepth            Q.E.D.
-- Lemma: siblingCost                    Q.E.D.
-- Lemma: leafDepthBound                 Q.E.D.
-- Lemma: sinkCost
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Step: 3                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating:
--   cost, count, depth, height, leafDepth, locate, outsideCost, outsideCount, outsideWeight,
--   plug, replace, replaceOutside, weight
-- [Proven] sinkCost :: Ɐc ∷ Context → Ɐa ∷ Integer → Ɐx ∷ Integer → Ɐy ∷ Integer → Bool
sinkCost :: TP (Proof (Forall "c" Context -> Forall "a" Integer -> Forall "x" Integer -> Forall "y" Integer -> SBool))
sinkCost = do
  rc <- recall replaceOutsideCost
  rd <- recall replaceOutsideDepth
  sc <- recall siblingCost
  lb <- recall leafDepthBound

  calc "sinkCost"
    (\(Forall c) (Forall a) (Forall x) (Forall y) ->
       a .> 0 .&& a .<= x .&& outsideCount a c .> 0 .&& deepest c .=>
       cost (plug (replaceOutside a x c) (sFork (sLeaf a) (sLeaf y))) .<=
       cost (plug c (sFork (sLeaf x) (sLeaf y)))) $ \c a x y ->
      let changed = replaceOutside a x c
      in [a .> 0, a .<= x, outsideCount a c .> 0, deepest c] |- cost (plug changed (sFork (sLeaf a) (sLeaf y))) .<= cost (plug c (sFork (sLeaf x) (sLeaf y)))
                                                             ?? sc `at` (Inst @"c" changed, Inst @"x" a, Inst @"y" y)
                                                             ?? sc `at` (Inst @"c" c, Inst @"x" x, Inst @"y" y)
                                                             ?? rd `at` (Inst @"c" c, Inst @"old" a, Inst @"new" x)
                                                             =: outsideCost changed + (depth c + 1) * (a+y) .<= outsideCost c + (depth c + 1) * (x+y)
                                                             ?? rc `at` (Inst @"c" c, Inst @"old" a, Inst @"new" x)
                                                             =: (x-a) * (leafDepth a (plug c (sLeaf 0)) - (depth c + 1)) .<= 0
                                                             ?? lb `at` (Inst @"t" (plug c (sLeaf 0)), Inst @"w" a)
                                                             =: sTrue
                                                             =: qed

-- | Place the smallest weight in the left sibling position, exchanging
-- within the pair if possible and otherwise looking outside it.
--
-- >>> unliteral $ placeFirst 1 $ literal $ SiblingPair Hole 3 1
-- Just (SiblingPair Hole 1 3)
placeFirst :: SInteger -> SSiblingPair -> SSiblingPair
placeFirst a p = [sCase| p of
    SiblingPair c x y | a .== x -> p
                      | a .== y -> sSiblingPair c a x
                      | True    -> sSiblingPair (replaceOutside a x c) a y
  |]

-- | Place the second smallest weight in the right sibling position.
-- Outside replacement protects the first slot, including when weights tie.
--
-- >>> unliteral $ placeSecond 1 $ deepestPair exampleTree
-- Just (SiblingPair (GoRight (Leaf 3) (GoRight (Leaf 5) Hole)) 1 1)
placeSecond :: SInteger -> SSiblingPair -> SSiblingPair
placeSecond b p = [sCase| p of
    SiblingPair c x y | b .== y -> p
                      | True    -> sSiblingPair (replaceOutside b y c) x b
  |]

-- | Multiplicities outside a context's hole are nonnegative.
--
-- >>> runTP outsideCountNonNegative
-- Lemma: countNonNegative           Q.E.D.
-- Lemma: outsideCountNonNegative    Q.E.D.
-- Functions proven terminating: count, outsideCount
-- [Proven] outsideCountNonNegative :: Ɐc ∷ Context → Ɐw ∷ Integer → Bool
outsideCountNonNegative :: TP (Proof (Forall "c" Context -> Forall "w" Integer -> SBool))
outsideCountNonNegative = do
  cn <- recall countNonNegative

  inductiveLemma "outsideCountNonNegative" (\(Forall c) (Forall w) -> outsideCount w c .>= 0) [proofOf cn]

-- | The surrounding context of a selected pair.
pairContext :: SSiblingPair -> SContext
pairContext p = [sCase| p of SiblingPair c _ _ -> c |]

-- | The weight at the first selected sibling position.
firstWeight :: SSiblingPair -> SInteger
firstWeight p = [sCase| p of SiblingPair _ x _ -> x |]

-- | The weight at the second selected sibling position.
secondWeight :: SSiblingPair -> SInteger
secondWeight p = [sCase| p of SiblingPair _ _ y -> y |]

-- | Swapping an outside occurrence into a deepest sibling slot preserves
-- multiplicities and the depth bound, while never increasing cost.
--
-- >>> runTP sinkCorrect
-- Lemma: sinkCost                       Q.E.D.
-- Lemma: replaceOutsideCount            Q.E.D.
-- Lemma: replaceOutsideDepth            Q.E.D. [Cached]
-- Lemma: replaceOutsideHeight           Q.E.D.
-- Lemma: countPlug                      Q.E.D. [Cached]
-- Lemma: sinkCorrect
--   Step: 1                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating:
--   cost, count, depth, height, leafDepth, locate, outsideCost, outsideCount, outsideWeight,
--   plug, replace, replaceOutside, weight
-- [Proven] sinkCorrect :: Ɐc ∷ Context → Ɐa ∷ Integer → Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐw ∷ Integer → Bool
sinkCorrect :: TP (Proof (Forall "c" Context -> Forall "a" Integer -> Forall "x" Integer
                      -> Forall "y" Integer -> Forall "w" Integer -> SBool))
sinkCorrect = do
  sc <- recall sinkCost
  rc <- recall replaceOutsideCount
  rd <- recall replaceOutsideDepth
  rh <- recall replaceOutsideHeight
  cp <- recall countPlug

  calc "sinkCorrect"
    (\(Forall c) (Forall a) (Forall x) (Forall y) (Forall w) ->
       a .> 0 .&& a .<= x .&& outsideCount a c .> 0 .&& deepest c .=>
       let changed = replaceOutside a x c
           before  = plug c       (sFork (sLeaf x) (sLeaf y))
           after   = plug changed (sFork (sLeaf a) (sLeaf y))
       in count w after .== count w before .&& cost after .<= cost before .&& deepest changed) $ \c a x y w ->
      let changed = replaceOutside a x c
          before  = plug c       (sFork (sLeaf x) (sLeaf y))
          after   = plug changed (sFork (sLeaf a) (sLeaf y))
      in [a .> 0, a .<= x, outsideCount a c .> 0, deepest c] |- count w after .== count w before .&& cost after .<= cost before .&& deepest changed
                                                             ?? sc `at` (Inst @"c" c, Inst @"a" a, Inst @"x" x, Inst @"y" y)
                                                             ?? rc `at` (Inst @"c" c, Inst @"old" a, Inst @"new" x, Inst @"w" w)
                                                             ?? rd `at` (Inst @"c" c, Inst @"old" a, Inst @"new" x)
                                                             ?? rh `at` (Inst @"c" c, Inst @"old" a, Inst @"new" x)
                                                             ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf x) (sLeaf y)), Inst @"w" w)
                                                             ?? cp `at` (Inst @"c" changed, Inst @"t" (sFork (sLeaf a) (sLeaf y)), Inst @"w" w)
                                                             =: sTrue
                                                             =: qed

-- | Installing the first minimum preserves the tree's multiset, does not
-- increase cost, and leaves the selected slots deepest.
--
-- >>> runTP placeFirstCorrect
-- Lemma: sinkCorrect                    Q.E.D.
-- Lemma: countPlug                      Q.E.D. [Cached]
-- Lemma: siblingCost                    Q.E.D. [Cached]
-- Lemma: placeFirstCorrect
--   Step: 1                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating:
--   cost, count, depth, height, leafDepth, locate, outsideCost, outsideCount, outsideWeight,
--   plug, replace, replaceOutside, weight
-- [Proven] placeFirstCorrect :: Ɐc ∷ Context → Ɐa ∷ Integer → Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐw ∷ Integer → Bool
placeFirstCorrect :: TP (Proof (Forall "c" Context -> Forall "a" Integer -> Forall "x" Integer
                            -> Forall "y" Integer -> Forall "w" Integer -> SBool))
placeFirstCorrect = do
  sc <- recall sinkCorrect
  cp <- recall countPlug
  cc <- recall siblingCost

  calc "placeFirstCorrect"
    (\(Forall c) (Forall a) (Forall x) (Forall y) (Forall w) ->
       let p = sSiblingPair c x y
           q = placeFirst a p
       in a .> 0 .&& a .<= x .&& a .<= y .&& count a (rebuildPair p) .> 0 .&& deepest c .=>
          firstWeight q .== a .&& count w (rebuildPair q) .== count w (rebuildPair p)
          .&& cost (rebuildPair q) .<= cost (rebuildPair p) .&& deepest (pairContext q)) $ \c a x y w ->
      let p = sSiblingPair c x y
          q = placeFirst a p
      in [a .> 0, a .<= x, a .<= y, count a (rebuildPair p) .> 0, deepest c] |- firstWeight q .== a .&& count w (rebuildPair q) .== count w (rebuildPair p)
                                                                                .&& cost (rebuildPair q) .<= cost (rebuildPair p) .&& deepest (pairContext q)
                                                                             ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf x) (sLeaf y)), Inst @"w" a)
                                                                             ?? sc `at` (Inst @"c" c, Inst @"a" a, Inst @"x" x, Inst @"y" y, Inst @"w" w)
                                                                             ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf x) (sLeaf y)), Inst @"w" w)
                                                                             ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf y) (sLeaf x)), Inst @"w" w)
                                                                             ?? cc `at` (Inst @"c" c, Inst @"x" x, Inst @"y" y)
                                                                             ?? cc `at` (Inst @"c" c, Inst @"x" y, Inst @"y" x)
                                                                             =: sTrue
                                                                             =: qed

-- | Installing the second minimum preserves the first, including the case
-- of equal minima: the occurrence count requires a separate copy for it.
--
-- >>> runTP placeSecondCorrect
-- Lemma: sinkCorrect                    Q.E.D.
-- Lemma: countPlug                      Q.E.D. [Cached]
-- Lemma: siblingCost                    Q.E.D. [Cached]
-- Lemma: placeSecondCorrect
--   Step: 1                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating:
--   cost, count, depth, height, leafDepth, locate, outsideCost, outsideCount, outsideWeight,
--   plug, replace, replaceOutside, weight
-- [Proven] placeSecondCorrect :: Ɐc ∷ Context → Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐy ∷ Integer → Ɐw ∷ Integer → Bool
placeSecondCorrect :: TP (Proof (Forall "c" Context -> Forall "a" Integer -> Forall "b" Integer
                             -> Forall "y" Integer -> Forall "w" Integer -> SBool))
placeSecondCorrect = do
  sc <- recall sinkCorrect
  cp <- recall countPlug
  cc <- recall siblingCost

  calc "placeSecondCorrect"
    (\(Forall c) (Forall a) (Forall b) (Forall y) (Forall w) ->
       let p = sSiblingPair c a y
           q = placeSecond b p
       in b .> 0 .&& b .<= y .&& count b (rebuildPair p) .>= 1 + ite (a .== b) 1 0 .&& deepest c .=>
          firstWeight q .== a .&& secondWeight q .== b
          .&& count w (rebuildPair q) .== count w (rebuildPair p)
          .&& cost (rebuildPair q) .<= cost (rebuildPair p)) $ \c a b y w ->
      let p = sSiblingPair c a y
          q = placeSecond b p
          changed = replaceOutside b y c
      in [b .> 0, b .<= y, count b (rebuildPair p) .>= 1 + ite (a .== b) 1 0, deepest c] |- firstWeight q .== a .&& secondWeight q .== b
                                                                                            .&& count w (rebuildPair q) .== count w (rebuildPair p)
                                                                                            .&& cost (rebuildPair q) .<= cost (rebuildPair p)
                                                                                         ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf a) (sLeaf y)), Inst @"w" b)
                                                                                         ?? sc `at` (Inst @"c" c, Inst @"a" b, Inst @"x" y, Inst @"y" a, Inst @"w" w)
                                                                                         ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf a) (sLeaf y)), Inst @"w" w)
                                                                                         ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf y) (sLeaf a)), Inst @"w" w)
                                                                                         ?? cp `at` (Inst @"c" changed, Inst @"t" (sFork (sLeaf a) (sLeaf b)), Inst @"w" w)
                                                                                         ?? cp `at` (Inst @"c" changed, Inst @"t" (sFork (sLeaf b) (sLeaf a)), Inst @"w" w)
                                                                                         ?? cc `at` (Inst @"c" c, Inst @"x" a, Inst @"y" y)
                                                                                         ?? cc `at` (Inst @"c" c, Inst @"x" y, Inst @"y" a)
                                                                                         ?? cc `at` (Inst @"c" changed, Inst @"x" a, Inst @"y" b)
                                                                                         ?? cc `at` (Inst @"c" changed, Inst @"x" b, Inst @"y" a)
                                                                                         =: sTrue
                                                                                         =: qed

-- | After placing the first minimum, the other selected slot can receive
-- the second. When the minima differ there is only one copy of the first.
--
-- >>> runTP remainingBound
-- Lemma: countPlug                  Q.E.D.
-- Lemma: outsideCountNonNegative    Q.E.D.
-- Lemma: remainingBound
--   Step: 1                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: count, outsideCount, plug, replace, replaceOutside
-- [Proven] remainingBound :: Ɐc ∷ Context → Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐx ∷ Integer → Ɐy ∷ Integer → Bool
remainingBound :: TP (Proof (Forall "c" Context -> Forall "a" Integer -> Forall "b" Integer
                         -> Forall "x" Integer -> Forall "y" Integer -> SBool))
remainingBound = do
  cp <- recall countPlug
  cn <- recall outsideCountNonNegative

  calc "remainingBound"
    (\(Forall c) (Forall a) (Forall b) (Forall x) (Forall y) ->
       a .<= b .&& a .<= x .&& a .<= y .&& (x .== a .|| b .<= x) .&& (y .== a .|| b .<= y)
       .&& (a .< b .=> count a (rebuildPair (sSiblingPair c x y)) .== 1) .=>
       b .<= secondWeight (placeFirst a (sSiblingPair c x y))) $ \c a b x y ->
      [a .<= b, a .<= x, a .<= y, x .== a .|| b .<= x, y .== a .|| b .<= y,
       a .< b .=> count a (rebuildPair (sSiblingPair c x y)) .== 1]
      |- b .<= secondWeight (placeFirst a (sSiblingPair c x y))
      ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf x) (sLeaf y)), Inst @"w" a)
      ?? cn `at` (Inst @"c" c, Inst @"w" a)
      =: sTrue
      =: qed

-- * The greedy-choice theorem

-- | The two smallest positive weights, counting occurrences rather than
-- distinct values. If they differ, the smallest occurs exactly once.
--
-- >>> prove $ smallestTwo 1 1 exampleTree
-- Q.E.D.
--
-- >>> prove $ sNot $ smallestTwo 1 3 exampleTree
-- Q.E.D.
--
-- >>> prove $ smallestTwo 1 2 $ replace 1 2 exampleTree
-- Q.E.D.
smallestTwo :: SInteger -> SInteger -> STree -> SBool
smallestTwo a b t = isFork t .&& a .> 0 .&& a .<= b
                .&& count a t .> 0 .&& count b t .>= 1 + ite (a .== b) 1 0
                .&& (a .< b .=> count a t .== 1)
                .&& quantifiedBool (\(Forall @"w" w) -> count w t .> 0 .=> a .<= w .&& (w .== a .|| b .<= w))

-- | Arrange the two minimum weights as siblings at maximum depth.
-- The precondition is 'smallestTwo'; 'greedyChoice' proves the resulting
-- tree preserves multiplicities and does not increase cost.
--
-- >>> unliteral $ rebuildPair $ greedyPair 1 1 exampleTree
-- Just (Fork (Leaf 3) (Fork (Leaf 5) (Fork (Leaf 1) (Leaf 1))))
--
-- >>> cost $ rebuildPair $ greedyPair 1 1 exampleTree
-- 19 :: SInteger
greedyPair :: SInteger -> SInteger -> STree -> SSiblingPair
greedyPair a b t = placeSecond b (placeFirst a (deepestPair t))

-- | Each selected leaf obeys the bounds on the two minimum weights.
--
-- >>> runTP selectedBounds
-- Lemma: deepestPairCorrect         Q.E.D.
-- Lemma: countPlug                  Q.E.D.
-- Lemma: outsideCountNonNegative    Q.E.D.
-- Lemma: selectedBounds
--   Step: 1                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: count, deepestPair, depth, height, outsideCount, plug
-- [Proven] selectedBounds :: Ɐt ∷ Tree → Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
selectedBounds :: TP (Proof (Forall "t" Tree -> Forall "a" Integer -> Forall "b" Integer -> SBool))
selectedBounds = do
  dp <- recall deepestPairCorrect
  cp <- recall countPlug
  cn <- recall outsideCountNonNegative

  calc "selectedBounds"
    (\(Forall t) (Forall a) (Forall b) ->
       let p = deepestPair t
           x = firstWeight p
           y = secondWeight p
       in smallestTwo a b t .=> a .<= x .&& a .<= y .&& (x .== a .|| b .<= x) .&& (y .== a .|| b .<= y)) $ \t a b ->
      let p = deepestPair t
          c = pairContext p
          x = firstWeight p
          y = secondWeight p
          leaves = sFork (sLeaf x) (sLeaf y)
      in [smallestTwo a b t] |- a .<= x .&& a .<= y .&& (x .== a .|| b .<= x) .&& (y .== a .|| b .<= y)
                             ?? dp `at` Inst @"t" t
                             ?? cp `at` (Inst @"c" c, Inst @"t" leaves, Inst @"w" x)
                             ?? cp `at` (Inst @"c" c, Inst @"t" leaves, Inst @"w" y)
                             ?? cn `at` (Inst @"c" c, Inst @"w" x)
                             ?? cn `at` (Inst @"c" c, Inst @"w" y)
                             =: sTrue
                             =: qed

-- | Huffman's greedy-choice lemma, for an arbitrary full binary tree:
-- the two minimum weights can be made siblings without increasing cost
-- or changing any leaf multiplicity. No tree-size bound is imposed.
-- 'huffmanOptimal' uses this step to reduce each competing tree before
-- applying its induction hypothesis.
--
-- >>> runTP greedyChoice
-- Lemma: deepestPairCorrect                       Q.E.D.
-- Lemma: deepestPairBound                         Q.E.D.
-- Lemma: selectedBounds                           Q.E.D.
-- Lemma: placeFirstCorrect                        Q.E.D.
-- Lemma: placeSecondCorrect                       Q.E.D.
-- Lemma: remainingBound                           Q.E.D.
-- Lemma: greedyChoice
--   Step: 1                                       Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating:
--   cost, count, deepestPair, depth, height, leafDepth, locate, outsideCost, outsideCount,
--   outsideWeight, plug, replace, replaceOutside, weight
-- [Proven] greedyChoice :: Ɐt ∷ Tree → Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐw ∷ Integer → Bool
greedyChoice :: TP (Proof (Forall "t" Tree -> Forall "a" Integer -> Forall "b" Integer -> Forall "w" Integer -> SBool))
greedyChoice = do
  dp <- recall deepestPairCorrect
  db <- recall deepestPairBound
  sb <- recall selectedBounds
  pf <- recall placeFirstCorrect
  ps <- recall placeSecondCorrect
  rb <- recall remainingBound

  calc "greedyChoice"
    (\(Forall t) (Forall a) (Forall b) (Forall w) ->
       let q = greedyPair a b t
       in smallestTwo a b t .=> firstWeight q .== a .&& secondWeight q .== b
          .&& count w (rebuildPair q) .== count w t .&& cost (rebuildPair q) .<= cost t) $ \t a b w ->
      let p = deepestPair t
          c = pairContext p
          x = firstWeight p
          y = secondWeight p
          p1 = placeFirst a p
          c1 = pairContext p1
          y1 = secondWeight p1
          q = greedyPair a b t
      in [smallestTwo a b t] |- firstWeight q .== a .&& secondWeight q .== b
                                .&& count w (rebuildPair q) .== count w t .&& cost (rebuildPair q) .<= cost t
                             ?? dp `at` Inst @"t" t
                             ?? db `at` Inst @"t" t
                             ?? sb `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b)
                             ?? pf `at` (Inst @"c" c, Inst @"a" a, Inst @"x" x, Inst @"y" y, Inst @"w" w)
                             ?? pf `at` (Inst @"c" c, Inst @"a" a, Inst @"x" x, Inst @"y" y, Inst @"w" b)
                             ?? rb `at` (Inst @"c" c, Inst @"a" a, Inst @"b" b, Inst @"x" x, Inst @"y" y)
                             ?? ps `at` (Inst @"c" c1, Inst @"a" a, Inst @"b" b, Inst @"y" y1, Inst @"w" w)
                             =: sTrue
                             =: qed

-- * The sorted frequency queue

-- | Multiplicity of a frequency in the input queue.
--
-- >>> frequencyCount 1 $ literal [1, 1, 3, 5]
-- 2 :: SInteger
frequencyCount :: SInteger -> SList Integer -> SInteger
frequencyCount = smtFunction "frequencyCount" $ \w xs -> [sCase| xs of
                                                            []     -> 0
                                                            x : ys -> ite (w .== x) 1 0 + frequencyCount w ys
                                                         |]

-- | Every frequency in the queue is at least the given lower bound.
--
-- >>> above 3 $ literal [3, 5]
-- True
above :: SInteger -> SList Integer -> SBool
above = smtFunction "above" $ \lo xs -> [sCase| xs of
                                           []     -> sTrue
                                           x : ys -> lo .<= x .&& above lo ys
                                        |]

-- | A nondecreasing queue of positive integer frequencies.
--
-- >>> ordered $ literal [1, 1, 3, 5]
-- True
--
-- >>> ordered $ literal [1, 0]
-- False
ordered :: SList Integer -> SBool
ordered = smtFunction "ordered" $ \xs -> [sCase| xs of
                                            []     -> sTrue
                                            x : ys -> x .> 0 .&& above x ys .&& ordered ys
                                         |]

-- | Insert a frequency into a sorted queue.
--
-- >>> unliteral $ insert 4 $ literal [1, 3, 5]
-- Just [1,3,4,5]
insert :: SInteger -> SList Integer -> SList Integer
insert = smtFunction "insert" $ \e xs -> [sCase| xs of
                                            []               -> [e]
                                            x : ys | e .<= x -> e .: xs
                                                   | True    -> x .: insert e ys
                                         |]

-- | Insertion adds one queue entry. This supplies the termination argument
-- for Huffman's recursion, where two entries are replaced by one.
--
-- >>> runTP insertLength
-- Lemma: insertLength    Q.E.D.
-- Functions proven terminating: insert
-- [Proven] insertLength :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Bool
insertLength :: TP (Proof (Forall "xs" [Integer] -> Forall "e" Integer -> SBool))
insertLength = inductiveLemma "insertLength" (\(Forall xs) (Forall e) -> L.length (insert e xs) .== 1 + L.length xs) []

-- | Queue multiplicities are nonnegative.
--
-- >>> runTP frequencyCountNonNegative
-- Lemma: frequencyCountNonNegative    Q.E.D.
-- Functions proven terminating: frequencyCount
-- [Proven] frequencyCountNonNegative :: Ɐxs ∷ [Integer] → Ɐw ∷ Integer → Bool
frequencyCountNonNegative :: TP (Proof (Forall "xs" [Integer] -> Forall "w" Integer -> SBool))
frequencyCountNonNegative = inductiveLemma "frequencyCountNonNegative" (\(Forall xs) (Forall w) -> frequencyCount w xs .>= 0) []

-- | Insertion changes exactly the multiplicity of the inserted frequency.
--
-- >>> runTP insertCount
-- Lemma: insertCount    Q.E.D.
-- Functions proven terminating: frequencyCount, insert
-- [Proven] insertCount :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Ɐw ∷ Integer → Bool
insertCount :: TP (Proof (Forall "xs" [Integer] -> Forall "e" Integer -> Forall "w" Integer -> SBool))
insertCount = inductiveLemma "insertCount" (\(Forall xs) (Forall e) (Forall w) -> frequencyCount w (insert e xs) .== frequencyCount w xs + ite (w .== e) 1 0) []

-- | Insertion preserves a lower bound precisely when the new entry meets it.
-- CVC5 handles the recursive sequence reasoning more readily than Z3.
--
-- >>> runTP insertAbove
-- Inductive lemma: insertAbove
--   Step: Base                    Q.E.D.
--   Step: 1                       Q.E.D.
--   Step: 2                       Q.E.D.
--   Result:                       Q.E.D.
-- Functions proven terminating: above, insert
-- [Proven] insertAbove :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Ɐlo ∷ Integer → Bool
insertAbove :: TP (Proof (Forall "xs" [Integer] -> Forall "e" Integer -> Forall "lo" Integer -> SBool))
insertAbove = inductWith cvc5 "insertAbove"
  (\(Forall xs) (Forall e) (Forall lo) -> above lo (insert e xs) .== (lo .<= e .&& above lo xs)) $ \ih (x, xs) e lo ->
    [] |- above lo (insert e (x .: xs))
       =: ite (e .<= x) (lo .<= e .&& lo .<= x .&& above lo xs) (lo .<= x .&& above lo (insert e xs))
       ?? ih `at` (Inst @"e" e, Inst @"lo" lo)
       =: lo .<= e .&& above lo (x .: xs)
       =: qed

-- | Lowering a queue's lower bound preserves the bound.
--
-- >>> runTP aboveWeaken
-- Lemma: aboveWeaken    Q.E.D.
-- Functions proven terminating: above
-- [Proven] aboveWeaken :: Ɐxs ∷ [Integer] → Ɐlo ∷ Integer → Ɐhi ∷ Integer → Bool
aboveWeaken :: TP (Proof (Forall "xs" [Integer] -> Forall "lo" Integer -> Forall "hi" Integer -> SBool))
aboveWeaken = inductiveLemma "aboveWeaken" (\(Forall xs) (Forall lo) (Forall hi) -> lo .<= hi .&& above hi xs .=> above lo xs) []

-- | Inserting a positive frequency preserves a sorted positive queue.
--
-- >>> runTP insertOrdered
-- Lemma: insertAbove                Q.E.D.
-- Lemma: aboveWeaken                Q.E.D.
-- Inductive lemma: insertOrdered
--   Step: Base                      Q.E.D.
--   Step: 1                         Q.E.D.
--   Step: 2                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: above, insert, ordered
-- [Proven] insertOrdered :: Ɐxs ∷ [Integer] → Ɐe ∷ Integer → Bool
insertOrdered :: TP (Proof (Forall "xs" [Integer] -> Forall "e" Integer -> SBool))
insertOrdered = do
  ia <- recall insertAbove
  aw <- recall aboveWeaken

  inductWith cvc5 "insertOrdered"
    (\(Forall xs) (Forall e) -> ordered xs .&& e .> 0 .=> ordered (insert e xs)) $ \ih (x, xs) e ->
      [ordered (x .: xs), e .> 0] |- ordered (insert e (x .: xs))
                                  =: ite (e .<= x) (e .> 0 .&& above e (x .: xs) .&& ordered (x .: xs))
                                                   (x .> 0 .&& above x (insert e xs) .&& ordered (insert e xs))
                                  ?? aw `at` (Inst @"xs" xs, Inst @"lo" e, Inst @"hi" x)
                                  ?? ia `at` (Inst @"xs" xs, Inst @"e" e, Inst @"lo" x)
                                  ?? ih `at` Inst @"e" e
                                  =: sTrue
                                  =: qed

-- | Any frequency occurring in a bounded queue satisfies its lower bound.
--
-- >>> runTP aboveCount
-- Lemma: aboveCount    Q.E.D.
-- Functions proven terminating: above, frequencyCount
-- [Proven] aboveCount :: Ɐxs ∷ [Integer] → Ɐlo ∷ Integer → Ɐw ∷ Integer → Bool
aboveCount :: TP (Proof (Forall "xs" [Integer] -> Forall "lo" Integer -> Forall "w" Integer -> SBool))
aboveCount = inductiveLemma "aboveCount" (\(Forall xs) (Forall lo) (Forall w) -> above lo xs .&& frequencyCount w xs .> 0 .=> lo .<= w) []

-- | Every frequency occurring in a sorted positive queue is positive.
--
-- >>> runTP orderedPositive
-- Lemma: orderedPositive    Q.E.D.
-- Functions proven terminating: above, frequencyCount, ordered
-- [Proven] orderedPositive :: Ɐxs ∷ [Integer] → Ɐw ∷ Integer → Bool
orderedPositive :: TP (Proof (Forall "xs" [Integer] -> Forall "w" Integer -> SBool))
orderedPositive = inductiveLemmaWith cvc5 "orderedPositive" (\(Forall xs) (Forall w) -> ordered xs .&& frequencyCount w xs .> 0 .=> w .> 0) []

-- * Huffman construction and its invariants

-- | Replace one occurrence of @a+b@ by sibling leaves @a@ and @b@.
-- The precondition is that the summed weight occurs in the tree.
--
-- >>> unliteral $ expand 1 1 $ sFork (sLeaf 2) (sLeaf 3)
-- Just (Fork (Fork (Leaf 1) (Leaf 1)) (Leaf 3))
expand :: SInteger -> SInteger -> STree -> STree
expand a b t = plug (locate (a+b) t) (sFork (sLeaf a) (sLeaf b))

-- | Construct a Huffman tree from a nonempty sorted positive queue.
-- The empty case is a placeholder, excluded by the correctness theorem.
-- Each recursive call removes the two minimum frequencies, inserts their sum,
-- and expands one occurrence of that sum in the resulting tree.
--
-- This is the recursive formulation commonly used in proofs. The usual
-- algorithm maintains a queue of trees and joins the two lightest; it can
-- produce a different tree shape with the same optimal cost. Here 'locate'
-- chooses the first leaf with the summed weight, even if an original input
-- frequency equals that sum. Any such leaf is suitable in this weight-only
-- model, which does not track the identities of symbols or merged subtrees.
--
-- >>> unliteral $ huffman $ literal [1, 1, 3, 5]
-- Just (Fork (Fork (Fork (Leaf 1) (Leaf 1)) (Leaf 3)) (Leaf 5))
--
-- >>> cost $ huffman $ literal [1, 1, 3, 5]
-- 17 :: SInteger
--
-- >>> cost $ huffman $ literal [5, 9, 12, 13, 16, 45]
-- 224 :: SInteger
--
-- >>> cost $ huffman $ literal [7]
-- 0 :: SInteger
huffman :: SList Integer -> STree
huffman = smtFunctionWithMeasure "huffman" (L.length, [measureLemma insertLength]) $ \xs ->
  [sCase| xs of
     []         -> sLeaf 0
     [a]        -> sLeaf a
     a : b : ys -> expand a b (huffman (insert (a+b) ys))
  |]

-- | Expanding a summed leaf removes one copy of the sum and adds the two
-- original frequencies. Coincident frequencies are counted with multiplicity.
--
-- >>> runTP expandCount
-- Lemma: locateCorrect       Q.E.D.
-- Lemma: countPlug           Q.E.D.
-- Lemma: expandCount
--   Step: 1                  Q.E.D.
--   Step: 2                  Q.E.D.
--   Result:                  Q.E.D.
-- Functions proven terminating: count, depth, leafDepth, locate, outsideCount, plug, replace
-- [Proven] expandCount :: Ɐt ∷ Tree → Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐw ∷ Integer → Bool
expandCount :: TP (Proof (Forall "t" Tree -> Forall "a" Integer -> Forall "b" Integer -> Forall "w" Integer -> SBool))
expandCount = do
  lc <- recall locateCorrect
  cp <- recall countPlug

  calc "expandCount"
    (\(Forall t) (Forall a) (Forall b) (Forall w) -> count (a+b) t .> 0 .=>
       count w (expand a b t) .== count w t - ite (w .== a+b) 1 0 + ite (w .== a) 1 0 + ite (w .== b) 1 0) $ \t a b w ->
      let c = locate (a+b) t
      in [count (a+b) t .> 0] |- count w (expand a b t)
                              ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf a) (sLeaf b)), Inst @"w" w)
                              =: outsideCount w c + ite (w .== a) 1 0 + ite (w .== b) 1 0
                              ?? lc `at` (Inst @"t" t, Inst @"w" (a+b), Inst @"new" (a+b))
                              ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf (a+b)), Inst @"w" w)
                              =: count w t - ite (w .== a+b) 1 0 + ite (w .== a) 1 0 + ite (w .== b) 1 0
                              =: qed

-- | Expanding a summed leaf increases cost by exactly the sum, independently
-- of where that occurrence lies in the tree.
--
-- >>> runTP expandCost
-- Lemma: locateCorrect                  Q.E.D.
-- Lemma: contraction                    Q.E.D.
-- Lemma: expandCost
--   Step: 1                             Q.E.D.
--   Step: 2                             Q.E.D.
--   Result:                             Q.E.D.
-- Functions proven terminating: cost, count, depth, leafDepth, locate, outsideCost, outsideWeight, plug, replace, weight
-- [Proven] expandCost :: Ɐt ∷ Tree → Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
expandCost :: TP (Proof (Forall "t" Tree -> Forall "a" Integer -> Forall "b" Integer -> SBool))
expandCost = do
  lc <- recall locateCorrect
  co <- recall contraction

  calc "expandCost"
    (\(Forall t) (Forall a) (Forall b) -> count (a+b) t .> 0 .=> cost (expand a b t) .== cost t + a+b) $ \t a b ->
      [count (a+b) t .> 0] |- cost (expand a b t)
                           ?? co `at` (Inst @"c" (locate (a+b) t), Inst @"a" a, Inst @"b" b)
                           =: cost (plug (locate (a+b) t) (sLeaf (a+b))) + a+b
                           ?? lc `at` (Inst @"t" t, Inst @"w" (a+b), Inst @"new" (a+b))
                           =: cost t + a+b
                           =: qed

-- | Huffman's construction preserves every input frequency, for any
-- nonempty queue. Sorting and positivity are needed only for optimality.
--
-- >>> runTP huffmanCounts
-- Lemma: insertLength                        Q.E.D.
-- Lemma: insertCount                         Q.E.D.
-- Lemma: frequencyCountNonNegative           Q.E.D.
-- Lemma: expandCount                         Q.E.D.
-- Inductive lemma (strong): huffmanCounts
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2                              Q.E.D.
--     Step: 1.3.1                            Q.E.D.
--     Step: 1.3.2                            Q.E.D.
--     Step: 1.3.3                            Q.E.D.
--     Step: 1.3.4                            Q.E.D.
--     Step: 1.3.5                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating:
--   count, depth, frequencyCount, huffman, insert, leafDepth, locate, outsideCount, plug, replace
-- [Proven] huffmanCounts :: Ɐxs ∷ [Integer] → Ɐw ∷ Integer → Bool
huffmanCounts :: TP (Proof (Forall "xs" [Integer] -> Forall "w" Integer -> SBool))
huffmanCounts = do
  il <- recall insertLength
  ic <- recall insertCount
  cn <- recall frequencyCountNonNegative
  ec <- recall expandCount

  sInductWith cvc5 "huffmanCounts"
    (\(Forall xs) (Forall w) -> sNot (L.null xs) .=> count w (huffman xs) .== frequencyCount w xs)
    (\xs _ -> L.length xs, []) $ \ih xs w ->
      [sNot (L.null xs)] |- count w (huffman xs)
                         =: [pCase| xs of
                               []         -> (0 :: SInteger) =: qed

                               [a]        -> ite (w .== a) (1 :: SInteger) 0 =: qed

                               a : b : ys -> let next = insert (a+b) ys
                                                 t    = huffman next
                                             in count w (expand a b t)
                                                ?? il `at` (Inst @"xs" ys, Inst @"e" (a+b))
                                                ?? ic `at` (Inst @"xs" ys, Inst @"e" (a+b), Inst @"w" (a+b))
                                                ?? cn `at` (Inst @"xs" ys, Inst @"w" (a+b))
                                                ?? ih `at` (Inst @"xs" next, Inst @"w" (a+b))
                                                ?? ec `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b, Inst @"w" w)
                                                =: count w t - ite (w .== a+b) 1 0 + ite (w .== a) 1 0 + ite (w .== b) 1 0
                                                ?? il `at` (Inst @"xs" ys, Inst @"e" (a+b))
                                                ?? ih `at` (Inst @"xs" next, Inst @"w" w)
                                                =: frequencyCount w next - ite (w .== a+b) 1 0 + ite (w .== a) 1 0 + ite (w .== b) 1 0
                                                ?? ic `at` (Inst @"xs" ys, Inst @"e" (a+b), Inst @"w" w)
                                                =: frequencyCount w ys + ite (w .== a) 1 0 + ite (w .== b) 1 0
                                                =: frequencyCount w (a .: b .: ys)
                                                =: qed
                            |]

-- | Cost recurrence of the constructed Huffman tree, justified by actually
-- expanding a leaf in the recursive result.
--
-- >>> runTP huffmanCostStep
-- Lemma: huffmanCounts                       Q.E.D.
-- Lemma: insertLength                        Q.E.D. [Cached]
-- Lemma: insertCount                         Q.E.D. [Cached]
-- Lemma: frequencyCountNonNegative           Q.E.D. [Cached]
-- Lemma: expandCost                          Q.E.D.
-- Lemma: huffmanCostStep
--   Step: 1                                  Q.E.D.
--   Step: 2                                  Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating:
--   cost, count, depth, frequencyCount, huffman, insert, leafDepth, locate, outsideCost,
--   outsideCount, outsideWeight, plug, replace, weight
-- [Proven] huffmanCostStep :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐxs ∷ [Integer] → Bool
huffmanCostStep :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "xs" [Integer] -> SBool))
huffmanCostStep = do
  hc <- recall huffmanCounts
  il <- recall insertLength
  ic <- recall insertCount
  cn <- recall frequencyCountNonNegative
  ec <- recall expandCost

  calcWith cvc5 "huffmanCostStep"
    (\(Forall a) (Forall b) (Forall xs) ->
       cost (huffman (a .: b .: xs)) .== cost (huffman (insert (a+b) xs)) + a+b) $ \a b xs ->
      let next = insert (a+b) xs
          t = huffman next
      in [] |- cost (huffman (a .: b .: xs))
            =: cost (expand a b t)
            ?? il `at` (Inst @"xs" xs, Inst @"e" (a+b))
            ?? ic `at` (Inst @"xs" xs, Inst @"e" (a+b), Inst @"w" (a+b))
            ?? cn `at` (Inst @"xs" xs, Inst @"w" (a+b))
            ?? hc `at` (Inst @"xs" next, Inst @"w" (a+b))
            ?? ec `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b)
            =: cost t + a+b
            =: qed

-- * Reducing a competing tree

-- | The tree and the frequency queue describe the same multiset of weights.
--
-- >>> prove $ sameWeights (literal [1, 1, 3, 5]) exampleTree
-- Q.E.D.
sameWeights :: SList Integer -> STree -> SBool
sameWeights xs t = quantifiedBool (\(Forall @"w" w) -> count w t .== frequencyCount w xs)

-- | All weights occurring in the tree are nonnegative.
--
-- >>> prove $ nonnegative exampleTree
-- Q.E.D.
nonnegative :: STree -> SBool
nonnegative t = quantifiedBool (\(Forall @"w" w) -> count w t .> 0 .=> w .>= 0)

-- | A tree with nonnegative leaf weights has nonnegative weight and cost.
--
-- >>> runTP nonnegativeCost
-- Lemma: countNonNegative    Q.E.D.
-- Lemma: nonnegativeCost     Q.E.D.
-- Functions proven terminating: cost, count, weight
-- [Proven] nonnegativeCost :: Ɐt ∷ Tree → Bool
nonnegativeCost :: TP (Proof (Forall "t" Tree -> SBool))
nonnegativeCost = do
  cn <- recall countNonNegative

  inductiveLemma "nonnegativeCost"
    (\(Forall t) -> nonnegative t .=> weight t .>= 0 .&& cost t .>= 0)
    [proofOf cn]

-- | Every competing tree for a sorted positive queue has nonnegative cost.
--
-- >>> runTP competitorCost
-- Lemma: orderedPositive     Q.E.D.
-- Lemma: nonnegativeCost     Q.E.D.
-- Lemma: competitorCost      Q.E.D.
-- Functions proven terminating: above, cost, count, frequencyCount, ordered, weight
-- [Proven] competitorCost :: Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Bool
competitorCost :: TP (Proof (Forall "xs" [Integer] -> Forall "t" Tree -> SBool))
competitorCost = do
  op <- recall orderedPositive
  nc <- recall nonnegativeCost

  lemmaWith cvc5 "competitorCost"
    (\(Forall xs) (Forall t) -> ordered xs .&& sameWeights xs t .=> cost t .>= 0)
    [proofOf op, proofOf nc]

-- | The first two queue entries bound every weight in a competing tree.
--
-- >>> runTP queueBounds
-- Lemma: aboveCount     Q.E.D.
-- Lemma: queueBounds
--   Step: 1             Q.E.D.
--   Result:             Q.E.D.
-- Functions proven terminating: above, count, frequencyCount, ordered
-- [Proven] queueBounds :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Ɐw ∷ Integer → Bool
queueBounds :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "xs" [Integer] -> Forall "t" Tree -> Forall "w" Integer -> SBool))
queueBounds = do
  ac <- recall aboveCount

  calcWith cvc5 "queueBounds"
    (\(Forall a) (Forall b) (Forall xs) (Forall t) (Forall w) ->
       ordered (a .: b .: xs) .&& sameWeights (a .: b .: xs) t .&& count w t .> 0 .=>
       a .<= w .&& (w .== a .|| b .<= w)) $ \a b xs t w ->
      [ordered (a .: b .: xs), sameWeights (a .: b .: xs) t, count w t .> 0] |- a .<= w .&& (w .== a .|| b .<= w)
                                                                             ?? ac `at` (Inst @"xs" xs, Inst @"lo" b, Inst @"w" w)
                                                                             =: sTrue
                                                                             =: qed

-- | The first two entries of a sorted positive queue satisfy the exact
-- minimum-weight precondition used by the tree exchange theorem.
--
-- >>> runTP queueMinima
-- Lemma: queueBounds                  Q.E.D.
-- Lemma: aboveCount                   Q.E.D. [Cached]
-- Lemma: frequencyCountNonNegative    Q.E.D.
-- Lemma: queueMinima                  Q.E.D.
-- Functions proven terminating: above, count, frequencyCount, ordered
-- [Proven] queueMinima :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Bool
queueMinima :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "xs" [Integer] -> Forall "t" Tree -> SBool))
queueMinima = do
  qb <- recall queueBounds
  ac <- recall aboveCount
  cn <- recall frequencyCountNonNegative

  lemmaWith cvc5 "queueMinima"
    (\(Forall a) (Forall b) (Forall xs) (Forall t) ->
       ordered (a .: b .: xs) .&& sameWeights (a .: b .: xs) t .=> smallestTwo a b t)
    [proofOf qb, proofOf ac, proofOf cn]

-- | Apply the greedy exchange to a competing tree, then contract its two
-- minimum-weight sibling leaves to their sum.
--
-- >>> unliteral $ contractGreedy 1 1 exampleTree
-- Just (Fork (Leaf 3) (Fork (Leaf 5) (Leaf 2)))
contractGreedy :: SInteger -> SInteger -> STree -> STree
contractGreedy a b t = plug (pairContext (greedyPair a b t)) (sLeaf (a+b))

-- | Exact frequency change after exchanging and contracting the minima.
--
-- >>> runTP contractGreedyCount
-- Lemma: greedyChoice                             Q.E.D.
-- Lemma: countPlug                                Q.E.D. [Cached]
-- Lemma: contractGreedyCount
--   Step: 1                                       Q.E.D.
--   Step: 2                                       Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating:
--   cost, count, deepestPair, depth, height, leafDepth, locate, outsideCost, outsideCount,
--   outsideWeight, plug, replace, replaceOutside, weight
-- [Proven] contractGreedyCount :: Ɐt ∷ Tree → Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐw ∷ Integer → Bool
contractGreedyCount :: TP (Proof (Forall "t" Tree -> Forall "a" Integer -> Forall "b" Integer -> Forall "w" Integer -> SBool))
contractGreedyCount = do
  gc <- recall greedyChoice
  cp <- recall countPlug

  calc "contractGreedyCount"
    (\(Forall t) (Forall a) (Forall b) (Forall w) -> smallestTwo a b t .=>
       count w (contractGreedy a b t) .== count w t - ite (w .== a) 1 0 - ite (w .== b) 1 0 + ite (w .== a+b) 1 0) $ \t a b w ->
      let c = pairContext (greedyPair a b t)
      in [smallestTwo a b t] |- count w (contractGreedy a b t)
                             ?? cp `at` (Inst @"c" c, Inst @"t" (sLeaf (a+b)), Inst @"w" w)
                             =: outsideCount w c + ite (w .== a+b) 1 0
                             ?? gc `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b, Inst @"w" w)
                             ?? cp `at` (Inst @"c" c, Inst @"t" (sFork (sLeaf a) (sLeaf b)), Inst @"w" w)
                             =: count w t - ite (w .== a) 1 0 - ite (w .== b) 1 0 + ite (w .== a+b) 1 0
                             =: qed

-- | Exchanging and contracting the minima saves at least their sum.
--
-- >>> runTP contractGreedyCost
-- Lemma: greedyChoice                             Q.E.D.
-- Lemma: contraction                              Q.E.D.
-- Lemma: contractGreedyCost
--   Step: 1                                       Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating:
--   cost, count, deepestPair, depth, height, leafDepth, locate, outsideCost, outsideCount,
--   outsideWeight, plug, replace, replaceOutside, weight
-- [Proven] contractGreedyCost :: Ɐt ∷ Tree → Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
contractGreedyCost :: TP (Proof (Forall "t" Tree -> Forall "a" Integer -> Forall "b" Integer -> SBool))
contractGreedyCost = do
  gc <- recall greedyChoice
  co <- recall contraction

  calc "contractGreedyCost"
    (\(Forall t) (Forall a) (Forall b) -> smallestTwo a b t .=> cost (contractGreedy a b t) + a+b .<= cost t) $ \t a b ->
      let c = pairContext (greedyPair a b t)
      in [smallestTwo a b t] |- cost (contractGreedy a b t) + a+b .<= cost t
                             ?? co `at` (Inst @"c" c, Inst @"a" a, Inst @"b" b)
                             ?? gc `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b, Inst @"w" a)
                             =: sTrue
                             =: qed

-- | One frequency's multiplicity agrees between the contracted competitor
-- and the next queue, including collisions with the newly inserted sum.
--
-- >>> runTP contractQueueCount
-- Lemma: queueMinima                              Q.E.D.
-- Lemma: contractGreedyCount                      Q.E.D.
-- Lemma: insertCount                              Q.E.D.
-- Lemma: contractQueueCount
--   Step: 1                                       Q.E.D.
--   Step: 2                                       Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating:
--   above, cost, count, deepestPair, depth, frequencyCount, height, insert, leafDepth,
--   locate, ordered, outsideCost, outsideCount, outsideWeight, plug, replace, replaceOutside, weight
-- [Proven] contractQueueCount :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Ɐw ∷ Integer → Bool
contractQueueCount :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "xs" [Integer]
                            -> Forall "t" Tree -> Forall "w" Integer -> SBool))
contractQueueCount = do
  qm <- recall queueMinima
  cc <- recall contractGreedyCount
  ic <- recall insertCount

  calcWith cvc5 "contractQueueCount"
    (\(Forall a) (Forall b) (Forall xs) (Forall t) (Forall w) ->
       ordered (a .: b .: xs) .&& sameWeights (a .: b .: xs) t .=>
       count w (contractGreedy a b t) .== frequencyCount w (insert (a+b) xs)) $ \a b xs t w ->
      [ordered (a .: b .: xs), sameWeights (a .: b .: xs) t] |- count w (contractGreedy a b t)
                                                             ?? qm `at` (Inst @"a" a, Inst @"b" b, Inst @"xs" xs, Inst @"t" t)
                                                             ?? cc `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b, Inst @"w" w)
                                                             =: frequencyCount w xs + ite (w .== a+b) 1 0
                                                             ?? ic `at` (Inst @"xs" xs, Inst @"e" (a+b), Inst @"w" w)
                                                             =: frequencyCount w (insert (a+b) xs)
                                                             =: qed

-- | The contracted competing tree matches the next Huffman queue.
--
-- >>> runTP contractGreedyWeights
-- Lemma: contractQueueCount                       Q.E.D.
-- Lemma: contractGreedyWeights                    Q.E.D.
-- Functions proven terminating:
--   above, cost, count, deepestPair, depth, frequencyCount, height, insert, leafDepth,
--   locate, ordered, outsideCost, outsideCount, outsideWeight, plug, replace, replaceOutside, weight
-- [Proven] contractGreedyWeights :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Bool
contractGreedyWeights :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "xs" [Integer] -> Forall "t" Tree -> SBool))
contractGreedyWeights = do
  cq <- recall contractQueueCount

  lemmaWith cvc5 "contractGreedyWeights"
    (\(Forall a) (Forall b) (Forall xs) (Forall t) -> ordered (a .: b .: xs) .&& sameWeights (a .: b .: xs) t .=> sameWeights (insert (a+b) xs) (contractGreedy a b t))
    [proofOf cq]

-- * Optimality and correctness

-- | The constructed Huffman tree is no more costly than any full binary
-- tree with the same positive frequencies. Strong induction is on queue
-- length; each recursive comparison uses the exchanged, contracted competitor.
--
-- >>> runTP huffmanOptimal
-- Lemma: insertLength                             Q.E.D.
-- Lemma: insertOrdered                            Q.E.D.
-- Lemma: huffmanCostStep                          Q.E.D.
-- Lemma: queueMinima                              Q.E.D.
-- Lemma: contractGreedyWeights                    Q.E.D.
-- Lemma: contractGreedyCost                       Q.E.D.
-- Lemma: competitorCost                           Q.E.D.
-- Inductive lemma (strong): huffmanOptimal
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                                   Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.3.1                                 Q.E.D.
--     Step: 1.3.2                                 Q.E.D.
--     Step: 1.3.3                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating:
--   above, cost, count, deepestPair, depth, frequencyCount, height, huffman, insert,
--   leafDepth, locate, ordered, outsideCost, outsideCount, outsideWeight, plug, replace,
--   replaceOutside, weight
-- [Proven] huffmanOptimal :: Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Bool
huffmanOptimal :: TP (Proof (Forall "xs" [Integer] -> Forall "t" Tree -> SBool))
huffmanOptimal = do
  il <- recall insertLength
  io <- recall insertOrdered
  hs <- recall huffmanCostStep
  qm <- recall queueMinima
  cw <- recall contractGreedyWeights
  cc <- recall contractGreedyCost
  nn <- recall competitorCost

  sInductWith cvc5 "huffmanOptimal"
    (\(Forall xs) (Forall t) -> ordered xs .&& sNot (L.null xs) .&& sameWeights xs t .=> cost (huffman xs) .<= cost t)
    (\xs _ -> L.length xs, []) $ \ih xs t ->
      [ordered xs, sNot (L.null xs), sameWeights xs t] |- cost (huffman xs) .<= cost t
                                                       =: [pCase| xs of
                                                             []         -> sTrue =: qed

                                                             [a]        -> (0 .<= cost t)
                                                                        ?? nn `at` (Inst @"xs" [a], Inst @"t" t)
                                                                        =: sTrue
                                                                        =: qed

                                                             a : b : ys -> let next    = insert (a+b) ys
                                                                               reduced = contractGreedy a b t
                                                                           in cost (huffman (a .: b .: ys)) .<= cost t
                                                                              ?? hs `at` (Inst @"a" a, Inst @"b" b, Inst @"xs" ys)
                                                                              =: cost (huffman next) + a+b .<= cost t
                                                                              ?? il `at` (Inst @"xs" ys, Inst @"e" (a+b))
                                                                              ?? io `at` (Inst @"xs" ys, Inst @"e" (a+b))
                                                                              ?? cw `at` (Inst @"a" a, Inst @"b" b, Inst @"xs" ys, Inst @"t" t)
                                                                              ?? ih `at` (Inst @"xs" next, Inst @"t" reduced)
                                                                              ?? qm `at` (Inst @"a" a, Inst @"b" b, Inst @"xs" ys, Inst @"t" t)
                                                                              ?? cc `at` (Inst @"t" t, Inst @"a" a, Inst @"b" b)
                                                                              =: sTrue
                                                                              =: qed
                                                          |]

-- | Correctness of Huffman's construction: it preserves the supplied
-- frequencies and minimizes weighted path length among all full binary trees
-- with those frequencies. The input must be nonempty, sorted, and positive.
--
-- >>> correctness
-- Lemma: huffmanCounts                            Q.E.D.
-- Lemma: huffmanOptimal                           Q.E.D.
-- Lemma: huffmanCorrect                           Q.E.D.
-- Functions proven terminating:
--   above, cost, count, deepestPair, depth, frequencyCount, height, huffman, insert,
--   leafDepth, locate, ordered, outsideCost, outsideCount, outsideWeight, plug, replace,
--   replaceOutside, weight
-- [Proven] huffmanCorrect :: Ɐxs ∷ [Integer] → Ɐt ∷ Tree → Bool
correctness :: IO (Proof (Forall "xs" [Integer] -> Forall "t" Tree -> SBool))
correctness = runTP $ do
  hc <- recall huffmanCounts
  ho <- recall huffmanOptimal

  lemmaWith cvc5 "huffmanCorrect"
    (\(Forall xs) (Forall t) -> ordered xs .&& sNot (L.null xs) .=>
       sameWeights xs (huffman xs) .&& (sameWeights xs t .=> cost (huffman xs) .<= cost t))
    [proofOf hc, proofOf ho]
