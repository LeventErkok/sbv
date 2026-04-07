-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Huffman
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving the roundtrip correctness of Huffman encoding: for any symbol @s@
-- that is a member of a binary tree @t@, decoding the encoded path yields @s@.
--
-- We also prove the optimality of the Huffman encoding: among all binary trees
-- with the same weighted symbols, the Huffman tree minimizes the weighted path
-- length (cost).
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

import Prelude hiding (null, head, tail, length)

import Data.SBV
import Data.SBV.List
import Data.SBV.TP
import Data.SBV.Tuple hiding (swap)

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Huffman tree

-- | A binary tree with weighted symbols at the leaves. The weight
-- represents the frequency of the symbol in the input.
data HTree = Tip { weight :: Integer
                 , symbol :: Integer
                 }
           | Bin { left   :: HTree
                 , right  :: HTree
                 }

-- | Create a symbolic version of HTree.
mkSymbolic [''HTree]

-- * Tree operations

-- | Size of a tree. Used as a termination measure for strong induction.
treeSize :: SHTree -> SInteger
treeSize = smtFunction "treeSize"
         $ \t -> [sCase| t of
                    Tip _ _ -> 1
                    Bin l r -> 1 + treeSize l + treeSize r
                 |]

-- | Check if a symbol is a member of the tree.
member :: SInteger -> SHTree -> SBool
member = smtFunction "member"
       $ \s t -> [sCase| t of
                    Tip _ x -> s .== x
                    Bin l r -> member s l .|| member s r
                 |]

-- * Encoding and decoding

-- | Encode a symbol by finding its path from root to leaf.
-- Returns a list of bits: 'sFalse' means go left, 'sTrue' means go right.
-- At a 'Tip', we return the empty path. At a 'Bin', we check membership
-- in the left subtree to decide which way to go.
findPath :: SInteger -> SHTree -> SList Bool
findPath = smtFunction "findPath"
         $ \s t -> [sCase| t of
                      Tip _ _ -> nil
                      Bin l r | member s l -> sFalse .: findPath s l
                              | True       -> sTrue  .: findPath s r
                   |]

-- | Decode a bit path through a tree, returning the symbol at the destination leaf.
-- At a 'Tip', we return the symbol (ignoring remaining bits). At a 'Bin',
-- we follow the first bit: 'sTrue' goes right, 'sFalse' goes left.
decode :: SList Bool -> SHTree -> SInteger
decode = smtFunction "decode"
       $ \bs t -> [sCase| t of
                     Tip _ x -> x
                     Bin l r -> case bs of
                                  -- Empty bit-string at an internal node shouldn't happen
                                  -- with a valid encoding. If it does due to a bug, we
                                  -- return an arbitrary value, which would invalidate proofs.
                                  []                -> some "unreachable" (const sTrue)
                                  b : rest | b      -> decode rest r
                                           | True   -> decode rest l
                  |]

-- * Correctness

-- | Roundtrip property: for any symbol @s@ that is a member of tree @t@,
-- decoding the encoded path yields @s@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) roundtrip
-- Lemma: treeSizePos                                Q.E.D.
-- Inductive lemma (strong): huffmanRoundtrip
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2 (2 way case split)
--       Step: 1.2.1.1                               Q.E.D.
--       Step: 1.2.1.2                               Q.E.D.
--       Step: 1.2.2.1                               Q.E.D.
--       Step: 1.2.2.2                               Q.E.D.
--       Step: 1.2.Completeness                      Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: decode, findPath, member, treeSize
-- [Proven] huffmanRoundtrip :: Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
roundtrip :: TP (Proof (Forall "s" Integer -> Forall "t" HTree -> SBool))
roundtrip = do
   tsPos <- inductiveLemma "treeSizePos"
                           (\(Forall @"t" t) -> treeSize t .>= 1)
                           []

   sInduct "huffmanRoundtrip"
     (\(Forall @"s" s) (Forall @"t" t) -> member s t .=> decode (findPath s t) t .== s)
     (\_ t -> treeSize t, [proofOf tsPos]) $
     \ih s t -> [member s t]
       |- decode (findPath s t) t .== s
       =: [pCase| t of
             Tip _ _ -> trivial

             Bin l r -> cases
               [ member s l
                   ==> decode (findPath s (sBin l r)) (sBin l r) .== s
                    ?? tsPos `at` Inst @"t" r
                    ?? ih `at` (Inst @"s" s, Inst @"t" l)
                    =: sTrue
                    =: qed

               , sNot (member s l)
                   ==> decode (findPath s (sBin l r)) (sBin l r) .== s
                    ?? tsPos `at` Inst @"t" l
                    ?? ih `at` (Inst @"s" s, Inst @"t" r)
                    =: sTrue
                    =: qed
               ]
          |]

-- * Optimality

-- | Total weight of a tree: sum of all leaf weights.
treeWeight :: SHTree -> SInteger
treeWeight = smtFunction "treeWeight"
           $ \t -> [sCase| t of
                      Tip w _ -> w
                      Bin l r -> treeWeight l + treeWeight r
                   |]

-- | Cost of a tree (weighted path length). This equals the sum over all leaves
-- of @weight(leaf) * depth(leaf)@, but is defined recursively: merging two
-- subtrees adds their combined weight to the cost.
cost :: SHTree -> SInteger
cost = smtFunction "cost"
     $ \t -> [sCase| t of
                Tip _ _ -> 0
                Bin l r -> cost l + cost r + treeWeight l + treeWeight r
             |]

-- | Number of leaves in a tree.
numLeaves :: SHTree -> SInteger
numLeaves = smtFunction "numLeaves"
          $ \t -> [sCase| t of
                     Tip _ _ -> 1
                     Bin l r -> numLeaves l + numLeaves r
                  |]

-- | Depth of a symbol in a tree. Returns 0 at the leaf containing the symbol.
-- At a 'Bin', we add 1 and recurse into the subtree containing the symbol.
depth :: SInteger -> SHTree -> SInteger
depth = smtFunction "depth"
      $ \s t -> [sCase| t of
                   Tip _ _ -> 0
                   Bin l r | member s l -> 1 + depth s l
                           | True       -> 1 + depth s r
                |]

-- | Swap two symbols (and their weights) in a tree. Given two leaves
-- identified by their (weight, symbol) pairs, this exchanges their
-- positions in the tree. The tree structure is preserved.
swap :: SInteger -> SInteger -> SInteger -> SInteger -> SHTree -> SHTree
swap = smtFunction "swap"
     $ \wa sa wb sb t ->
         [sCase| t of
            Tip w s | s .== sa .&& w .== wa -> sTip wb sb
                    | s .== sb .&& w .== wb -> sTip wa sa
                    | True                  -> sTip w s
            Bin l r -> sBin (swap wa sa wb sb l) (swap wa sa wb sb r)
         |]

-- | Count leaves matching a specific (weight, symbol) pair.
countWS :: SInteger -> SInteger -> SHTree -> SInteger
countWS = smtFunction "countWS"
        $ \w s t -> [sCase| t of
                       Tip tw ts -> ite (w .== tw .&& s .== ts) 1 0
                       Bin l r   -> countWS w s l + countWS w s r
                    |]

-- ** Swap lemmas
--
-- The key algebraic fact underlying Huffman optimality: swapping two leaves
-- changes the cost by @(wb - wa) * (depth(sa, T) - depth(sb, T))@. Therefore,
-- if the lighter symbol is deeper, swapping it with a heavier shallower symbol
-- does not increase cost.

-- | General weight formula for swap: the change in tree weight equals
-- @(wb - wa)@ times the count of @(wa, sa)@ leaves, plus @(wa - wb)@ times
-- the count of @(wb, sb)@ leaves. In particular, when each pair occurs exactly
-- once, the changes cancel and weight is preserved.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapWeight
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: distFold                                   Q.E.D.
-- Lemma: countWSBin                                 Q.E.D.
-- Lemma: mulCong                                    Q.E.D.
-- Lemma: tipHelper                                  Q.E.D.
-- Inductive lemma (strong): swapWeight
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1 (3 way case split)
--       Step: 1.1.1.1                               Q.E.D.
--       Step: 1.1.1.2                               Q.E.D.
--       Step: 1.1.1.3                               Q.E.D.
--       Step: 1.1.1.4                               Q.E.D.
--       Step: 1.1.2.1                               Q.E.D.
--       Step: 1.1.2.2                               Q.E.D.
--       Step: 1.1.2.3                               Q.E.D.
--       Step: 1.1.2.4                               Q.E.D.
--       Step: 1.1.3.1                               Q.E.D.
--       Step: 1.1.3.2                               Q.E.D.
--       Step: 1.1.3.3                               Q.E.D.
--       Step: 1.1.Completeness                      Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (apply IH for l)                  Q.E.D.
--     Step: 1.2.3 (apply IH for r)                  Q.E.D.
--     Step: 1.2.4 (regroup)                         Q.E.D.
--     Step: 1.2.5                                   Q.E.D.
--     Step: 1.2.6                                   Q.E.D.
--     Step: 1.2.7                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, swap, treeSize, treeWeight
-- [Proven] swapWeight :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapWeight :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                         -> Forall "wb" Integer -> Forall "sb" Integer
                         -> Forall "t"  HTree   -> SBool))
swapWeight = do
   tsPos <- inductiveLemma "treeSizePos"
                           (\(Forall @"t" t) -> treeSize t .>= 1)
                           []

   distFold <- lemma "distFold"
                     (\(Forall @"a" a) (Forall @"x" x) (Forall @"y" y) (Forall @"z" z) ->
                         x + y .== z .=> a * x + a * y .== a * z)
                     []

   cwsBin   <- inductiveLemma "countWSBin"
                  (\(Forall @"w" w) (Forall @"s" s) (Forall @"l" l) (Forall @"r" r) ->
                     countWS w s l + countWS w s r .== countWS w s (sBin l r))
                  []

   mulCong   <- lemma "mulCong"
                    (\(Forall @"a" a) (Forall @"x" x) (Forall @"y" y) -> x .== y .=> a * x .== a * y)
                    []

   tipHelper <- lemma "tipHelper"
                      (\(Forall @"a" a) (Forall @"b" b) (Forall @"p" p) (Forall @"q" q) ->
                          (a + b .== 0 .&& p .== 1 .&& (a .== 0 .|| q .== 0)) .=> a * p + b * q .== a)
                      []

   sInduct "swapWeight"
     (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
         treeWeight (swap wa sa wb sb t) .== treeWeight t
                                           + (wb - wa) * countWS wa sa t
                                           + (wa - wb) * countWS wb sb t)
     (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
     \ih wa sa wb sb t -> []
       |- [pCase| t of
             Tip w s -> treeWeight (swap wa sa wb sb t)
                     =: cases
                       [ s .== sa .&& w .== wa
                           ==> treeWeight (sTip wb sb)
                            =: wb
                            =: w + (wb - wa)
                            ?? tipHelper `at` ( Inst @"a" (wb - wa), Inst @"b" (wa - wb)
                                              , Inst @"p" (countWS wa sa t)
                                              , Inst @"q" (countWS wb sb t)
                                              )
                            =: w + (wb - wa) * countWS wa sa t + (wa - wb) * countWS wb sb t
                            =: qed

                       , sNot (s .== sa .&& w .== wa) .&& s .== sb .&& w .== wb
                           ==> treeWeight (sTip wa sa)
                            =: wa
                            =: w + (wa - wb)
                            ?? tipHelper `at` ( Inst @"a" (wa - wb), Inst @"b" (wb - wa)
                                              , Inst @"p" (countWS wb sb t)
                                              , Inst @"q" (countWS wa sa t)
                                              )
                            =: w + (wa - wb) * countWS wb sb t + (wb - wa) * countWS wa sa t
                            =: qed

                       , sNot (s .== sa .&& w .== wa) .&& sNot (s .== sb .&& w .== wb)
                           ==> treeWeight (sTip w s)
                            =: w
                            ?? mulCong `at` (Inst @"a" (wb - wa), Inst @"x" (countWS wa sa t), Inst @"y" (0 :: SInteger))
                            ?? mulCong `at` (Inst @"a" (wa - wb), Inst @"x" (countWS wb sb t), Inst @"y" (0 :: SInteger))
                            =: w + (wb - wa) * countWS wa sa t + (wa - wb) * countWS wb sb t
                            =: qed
                       ]

             Bin l r -> treeWeight (swap wa sa wb sb t)
                     -- unfold swap and treeWeight at Bin
                     =: treeWeight (swap wa sa wb sb l) + treeWeight (swap wa sa wb sb r)

                     ?? "apply IH for l"
                     ?? tsPos `at` Inst @"t" r
                     ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                     =: treeWeight l
                     + (wb - wa) * countWS wa sa l
                     + (wa - wb) * countWS wb sb l
                     + treeWeight (swap wa sa wb sb r)

                     ?? "apply IH for r"
                     ?? tsPos `at` Inst @"t" l
                     ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                     =: treeWeight l
                     + (wb - wa) * countWS wa sa l
                     + (wa - wb) * countWS wb sb l
                     + treeWeight r
                     + (wb - wa) * countWS wa sa r
                     + (wa - wb) * countWS wb sb r

                     ?? "regroup"
                     =: (treeWeight l + treeWeight r)
                     + ((wb - wa) * countWS wa sa l + (wb - wa) * countWS wa sa r)
                     + ((wa - wb) * countWS wb sb l + (wa - wb) * countWS wb sb r)

                     ?? cwsBin   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"l" l, Inst @"r" r)
                     ?? distFold `at` ( Inst @"a" (wb - wa), Inst @"x" (countWS wa sa l)
                                      , Inst @"y" (countWS wa sa r), Inst @"z" (countWS wa sa (sBin l r)))
                     =: (treeWeight l + treeWeight r)
                     + (wb - wa) * countWS wa sa (sBin l r)
                     + ((wa - wb) * countWS wb sb l + (wa - wb) * countWS wb sb r)

                     ?? cwsBin   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"l" l, Inst @"r" r)
                     ?? distFold `at` ( Inst @"a" (wa - wb), Inst @"x" (countWS wb sb l)
                                      , Inst @"y" (countWS wb sb r), Inst @"z" (countWS wb sb (sBin l r)))
                     =: (treeWeight l + treeWeight r)
                     + (wb - wa) * countWS wa sa (sBin l r)
                     + (wa - wb) * countWS wb sb (sBin l r)

                     ?? mulCong `at` (Inst @"a" (wb - wa), Inst @"x" (countWS wa sa (sBin l r)), Inst @"y" (countWS wa sa t))
                     ?? mulCong `at` (Inst @"a" (wa - wb), Inst @"x" (countWS wb sb (sBin l r)), Inst @"y" (countWS wb sb t))
                     =: treeWeight t + (wb - wa) * countWS wa sa t + (wa - wb) * countWS wb sb t
                     =: qed
          |]

-- ** Swap cost lemma
--
-- The cost analogue of 'swapWeight': swapping two leaves changes the cost
-- by a linear combination of their depth sums. Combined with 'swapWeight',
-- this shows that swapping a heavier-deeper leaf with a lighter-shallower
-- one does not increase cost — the key exchange argument for Huffman optimality.

-- | Weighted depth sum: total depth of all leaves matching a (weight, symbol)
-- pair. At a 'Tip', the depth is 0. At a 'Bin', each matching leaf's depth
-- increases by 1, accounted for by adding 'countWS'.
depthSum :: SInteger -> SInteger -> SHTree -> SInteger
depthSum = smtFunction "depthSum"
         $ \w s t -> [sCase| t of
                        Tip _ _ -> 0
                        Bin l r -> depthSum w s l + countWS w s l
                                 + depthSum w s r + countWS w s r
                     |]

-- | Swap cost lemma: swapping two leaves changes the cost by a linear
-- combination of their depth sums, paralleling 'swapWeight'. This is the
-- key algebraic fact underlying Huffman optimality.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapCost
-- Lemma: swapWeight                                 Q.E.D.
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: depthSumBin                                Q.E.D.
-- Lemma: factor4                                    Q.E.D.
-- Lemma: mulCong                                    Q.E.D.
-- Inductive lemma (strong): swapCost
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1 (3 way case split)
--       Step: 1.1.1.1                               Q.E.D.
--       Step: 1.1.1.2                               Q.E.D.
--       Step: 1.1.1.3                               Q.E.D.
--       Step: 1.1.2.1                               Q.E.D.
--       Step: 1.1.2.2                               Q.E.D.
--       Step: 1.1.2.3                               Q.E.D.
--       Step: 1.1.3.1                               Q.E.D.
--       Step: 1.1.3.2                               Q.E.D.
--       Step: 1.1.3.3                               Q.E.D.
--       Step: 1.1.Completeness                      Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (apply swapCost IH for l)         Q.E.D.
--     Step: 1.2.3 (apply swapCost IH for r)         Q.E.D.
--     Step: 1.2.4 (apply swapWeight for l)          Q.E.D.
--     Step: 1.2.5 (apply swapWeight for r)          Q.E.D.
--     Step: 1.2.6 (regroup)                         Q.E.D.
--     Step: 1.2.7 (fold depthSum for (wa, sa))      Q.E.D.
--     Step: 1.2.8 (fold depthSum for (wb, sb))      Q.E.D.
--     Step: 1.2.9                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: cost, countWS, depthSum, swap, treeSize, treeWeight
-- [Proven] swapCost :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapCost :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                       -> Forall "wb" Integer -> Forall "sb" Integer
                       -> Forall "t"  HTree   -> SBool))
swapCost = do
   swpW <- recall swapWeight

   tsPos <- inductiveLemma "treeSizePos"
                           (\(Forall @"t" t) -> treeSize t .>= 1)
                           []

   dsBin <- inductiveLemma "depthSumBin"
                (\(Forall @"w" w) (Forall @"s" s) (Forall @"l" l) (Forall @"r" r) ->
                   depthSum w s l + countWS w s l + depthSum w s r + countWS w s r
                     .== depthSum w s (sBin l r))
                []

   factor4 <- lemma "factor4"
                    (\(Forall @"a" a) (Forall @"x" x) (Forall @"y" y)
                     (Forall @"u" u) (Forall @"v" v) ->
                        a * x + a * y + a * u + a * v .== a * (x + y + u + v))
                    []

   mulCong <- lemma "mulCong"
                    (\(Forall @"a" a) (Forall @"x" x) (Forall @"y" y) ->
                        x .== y .=> a * x .== a * y)
                    []

   sInduct "swapCost"
     (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb)
      (Forall @"t" t) ->
         cost (swap wa sa wb sb t) .== cost t
                                     + (wb - wa) * depthSum wa sa t
                                     + (wa - wb) * depthSum wb sb t)
     (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
     \ih wa sa wb sb t -> []
       |- [pCase| t of
             Tip w s -> cost (swap wa sa wb sb t)
                     =: cases
                       [ s .== sa .&& w .== wa
                           ==> cost (sTip wb sb)
                            =: (0 :: SInteger)
                            ?? mulCong `at` (Inst @"a" (wb - wa), Inst @"x" (depthSum wa sa t), Inst @"y" (0 :: SInteger))
                            ?? mulCong `at` (Inst @"a" (wa - wb), Inst @"x" (depthSum wb sb t), Inst @"y" (0 :: SInteger))
                            =: cost t + (wb - wa) * depthSum wa sa t + (wa - wb) * depthSum wb sb t
                            =: qed

                       , sNot (s .== sa .&& w .== wa) .&& s .== sb .&& w .== wb
                           ==> cost (sTip wa sa)
                            =: (0 :: SInteger)
                            ?? mulCong `at` (Inst @"a" (wb - wa), Inst @"x" (depthSum wa sa t), Inst @"y" (0 :: SInteger))
                            ?? mulCong `at` (Inst @"a" (wa - wb), Inst @"x" (depthSum wb sb t), Inst @"y" (0 :: SInteger))
                            =: cost t + (wb - wa) * depthSum wa sa t + (wa - wb) * depthSum wb sb t
                            =: qed

                       , sNot (s .== sa .&& w .== wa) .&& sNot (s .== sb .&& w .== wb)
                           ==> cost (sTip w s)
                            =: (0 :: SInteger)
                            ?? mulCong `at` (Inst @"a" (wb - wa), Inst @"x" (depthSum wa sa t), Inst @"y" (0 :: SInteger))
                            ?? mulCong `at` (Inst @"a" (wa - wb), Inst @"x" (depthSum wb sb t), Inst @"y" (0 :: SInteger))
                            =: cost t + (wb - wa) * depthSum wa sa t + (wa - wb) * depthSum wb sb t
                            =: qed
                       ]

             Bin l r -> cost (swap wa sa wb sb t)
                     -- unfold swap and cost at Bin
                     =: cost (swap wa sa wb sb l) + cost (swap wa sa wb sb r)
                      + treeWeight (swap wa sa wb sb l) + treeWeight (swap wa sa wb sb r)

                     ?? "apply swapCost IH for l"
                     ?? tsPos `at` Inst @"t" r
                     ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                     =: cost l + (wb - wa) * depthSum wa sa l + (wa - wb) * depthSum wb sb l
                      + cost (swap wa sa wb sb r)
                      + treeWeight (swap wa sa wb sb l) + treeWeight (swap wa sa wb sb r)

                     ?? "apply swapCost IH for r"
                     ?? tsPos `at` Inst @"t" l
                     ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                     =: cost l + (wb - wa) * depthSum wa sa l + (wa - wb) * depthSum wb sb l
                      + cost r + (wb - wa) * depthSum wa sa r + (wa - wb) * depthSum wb sb r
                      + treeWeight (swap wa sa wb sb l) + treeWeight (swap wa sa wb sb r)

                     ?? "apply swapWeight for l"
                     ?? swpW `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                     =: cost l + (wb - wa) * depthSum wa sa l + (wa - wb) * depthSum wb sb l
                      + cost r + (wb - wa) * depthSum wa sa r + (wa - wb) * depthSum wb sb r
                      + treeWeight l + (wb - wa) * countWS wa sa l + (wa - wb) * countWS wb sb l
                      + treeWeight (swap wa sa wb sb r)

                     ?? "apply swapWeight for r"
                     ?? swpW `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                     =: cost l + (wb - wa) * depthSum wa sa l + (wa - wb) * depthSum wb sb l
                      + cost r + (wb - wa) * depthSum wa sa r + (wa - wb) * depthSum wb sb r
                      + treeWeight l + (wb - wa) * countWS wa sa l + (wa - wb) * countWS wb sb l
                      + treeWeight r + (wb - wa) * countWS wa sa r + (wa - wb) * countWS wb sb r

                     ?? "regroup"
                     =: (cost l + cost r + treeWeight l + treeWeight r)
                      + (wb - wa) * depthSum wa sa l + (wb - wa) * countWS wa sa l
                      + (wb - wa) * depthSum wa sa r + (wb - wa) * countWS wa sa r
                      + (wa - wb) * depthSum wb sb l + (wa - wb) * countWS wb sb l
                      + (wa - wb) * depthSum wb sb r + (wa - wb) * countWS wb sb r

                     ?? "fold depthSum for (wa, sa)"
                     ?? dsBin   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"l" l, Inst @"r" r)
                     ?? factor4 `at` ( Inst @"a" (wb - wa), Inst @"x" (depthSum wa sa l)
                                     , Inst @"y" (countWS wa sa l), Inst @"u" (depthSum wa sa r)
                                     , Inst @"v" (countWS wa sa r))
                     ?? mulCong `at` ( Inst @"a" (wb - wa)
                                     , Inst @"x" (depthSum wa sa l + countWS wa sa l
                                                 + depthSum wa sa r + countWS wa sa r)
                                     , Inst @"y" (depthSum wa sa (sBin l r)))
                     =: (cost l + cost r + treeWeight l + treeWeight r)
                      + (wb - wa) * depthSum wa sa (sBin l r)
                      + (wa - wb) * depthSum wb sb l + (wa - wb) * countWS wb sb l
                      + (wa - wb) * depthSum wb sb r + (wa - wb) * countWS wb sb r

                     ?? "fold depthSum for (wb, sb)"
                     ?? dsBin   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"l" l, Inst @"r" r)
                     ?? factor4 `at` ( Inst @"a" (wa - wb), Inst @"x" (depthSum wb sb l)
                                     , Inst @"y" (countWS wb sb l), Inst @"u" (depthSum wb sb r)
                                     , Inst @"v" (countWS wb sb r))
                     ?? mulCong `at` ( Inst @"a" (wa - wb)
                                     , Inst @"x" (depthSum wb sb l + countWS wb sb l
                                                 + depthSum wb sb r + countWS wb sb r)
                                     , Inst @"y" (depthSum wb sb (sBin l r)))
                     =: (cost l + cost r + treeWeight l + treeWeight r)
                      + (wb - wa) * depthSum wa sa (sBin l r)
                      + (wa - wb) * depthSum wb sb (sBin l r)

                     ?? mulCong `at` (Inst @"a" (wb - wa), Inst @"x" (depthSum wa sa (sBin l r)), Inst @"y" (depthSum wa sa t))
                     ?? mulCong `at` (Inst @"a" (wa - wb), Inst @"x" (depthSum wb sb (sBin l r)), Inst @"y" (depthSum wb sb t))
                     =: cost t + (wb - wa) * depthSum wa sa t + (wa - wb) * depthSum wb sb t
                     =: qed
          |]

-- ** Cost reduction corollary
--
-- If the heavier symbol is deeper (has a larger depth sum), swapping the two
-- does not increase cost. This is the exchange argument: any tree where a
-- heavier symbol sits below a lighter one can be improved by swapping them.

-- | Cost reduction: when @wb >= wa@ (b is at least as heavy) and b is at least
-- as deep (@depthSum(wb,sb,t) >= depthSum(wa,sa,t)@), swapping does not increase cost.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapReducesCost
-- Lemma: swapCost                                   Q.E.D.
-- Inductive lemma (strong): signProd
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                   Q.E.D.
--     Step: 1.1.2                                   Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Lemma: swapReducesCost
--   Step: 1                                         Q.E.D.
--   Step: 2                                         Q.E.D.
--   Step: 3                                         Q.E.D.
--   Step: 4                                         Q.E.D.
--   Step: 5                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: cost, countWS, depthSum, swap, treeSize, treeWeight
-- [Proven] swapReducesCost :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapReducesCost :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                              -> Forall "wb" Integer -> Forall "sb" Integer
                              -> Forall "t"  HTree   -> SBool))
swapReducesCost = do
   swpC <- recall swapCost

   signProd <- sInduct "signProd"
       (\(Forall @"a" a) (Forall @"b" b) ->
           a .>= 0 .&& b .<= 0 .=> a * b .<= 0)
       (\a _ -> ite (a .>= 0) a 0, []) $
       \ih a b -> [a .>= 0, b .<= 0]
         |- a * b .<= (0 :: SInteger)
         =: cases
              [ a .== 0 ==> (0 :: SInteger) * b .<= (0 :: SInteger) =: sTrue =: qed
              , a .>= 1 ==> (a - 1) * b + b .<= (0 :: SInteger)
                         ?? ih `at` (Inst @"a" (a - 1), Inst @"b" b)
                         =: sTrue
                         =: qed
              ]

   calc "swapReducesCost"
     (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
         wb .>= wa .&& depthSum wb sb t .>= depthSum wa sa t
           .=> cost (swap wa sa wb sb t) .<= cost t) $
     \wa sa wb sb t -> [wb .>= wa, depthSum wb sb t .>= depthSum wa sa t]
       |- cost (swap wa sa wb sb t) .<= cost t
       ?? swpC `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
       =: cost t + (wb - wa) * depthSum wa sa t + (wa - wb) * depthSum wb sb t .<= cost t
       =: (wb - wa) * depthSum wa sa t + (wa - wb) * depthSum wb sb t .<= (0 :: SInteger)
       =: (wb - wa) * depthSum wa sa t - (wb - wa) * depthSum wb sb t .<= (0 :: SInteger)
       =: (wb - wa) * (depthSum wa sa t - depthSum wb sb t) .<= (0 :: SInteger)
       ?? signProd `at` (Inst @"a" (wb - wa), Inst @"b" (depthSum wa sa t - depthSum wb sb t))
       =: sTrue
       =: qed

-- ** Greedy choice helpers
--
-- To state and prove the greedy choice property, we need to identify the deepest
-- sibling pair in a tree and show that the two lightest symbols can be swapped
-- into those positions without increasing cost.

-- | Height of a tree: the maximum depth of any leaf.
height :: SHTree -> SInteger
height = smtFunction "height"
       $ \t -> [sCase| t of
                  Tip _ _ -> 0
                  Bin l r -> 1 + ite (height l .>= height r) (height l) (height r)
               |]

-- | Weight of a deepest leaf (left-biased tie-breaking).
deepW :: SHTree -> SInteger
deepW = smtFunction "deepW"
      $ \t -> [sCase| t of
                 Tip w _ -> w
                 Bin l r -> ite (height l .>= height r) (deepW l) (deepW r)
              |]

-- | Symbol of a deepest leaf (left-biased tie-breaking).
deepS :: SHTree -> SInteger
deepS = smtFunction "deepS"
      $ \t -> [sCase| t of
                 Tip _ s -> s
                 Bin l r -> ite (height l .>= height r) (deepS l) (deepS r)
              |]

-- | Weight of the sibling of the deepest leaf. When the deeper subtree
-- is itself a leaf (height 0), the sibling is the other child; otherwise
-- we recurse into the deeper subtree.
sibW :: SHTree -> SInteger
sibW = smtFunction "sibW"
     $ \t -> [sCase| t of
                Tip w _ -> w
                Bin l r | height l .>= height r .&& height l .== 0 -> deepW r
                        | height l .>= height r                    -> sibW l
                        | height r .== 0                           -> deepW l
                        | True                                     -> sibW r
             |]

-- | Symbol of the sibling of the deepest leaf.
sibS :: SHTree -> SInteger
sibS = smtFunction "sibS"
     $ \t -> [sCase| t of
                Tip _ s -> s
                Bin l r | height l .>= height r .&& height l .== 0 -> deepS r
                        | height l .>= height r                    -> sibS l
                        | height r .== 0                           -> deepS l
                        | True                                     -> sibS r
             |]

-- ** Shared helper proofs
--
-- Commonly needed structural lemmas, extracted as standalone proofs so they
-- can be recalled by multiple proof groups without code duplication.

-- | Every tree has at least one node: @treeSize t >= 1@.
--
-- >>> runTPWith cvc5 treeSizePosProof
-- Lemma: treeSizePos                      Q.E.D.
-- Functions proven terminating: treeSize
-- [Proven] treeSizePos :: Ɐt ∷ HTree → Bool
treeSizePosProof :: TP (Proof (Forall "t" HTree -> SBool))
treeSizePosProof = inductiveLemma "treeSizePos" (\(Forall @"t" t) -> treeSize t .>= 1) []

-- | Leaf counts are non-negative: @countWS w s t >= 0@.
--
-- >>> runTPWith cvc5 countWSNonNegProof
-- Lemma: treeSizePos                      Q.E.D.
-- Inductive lemma (strong): countWSNonNeg
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: countWS, treeSize
-- [Proven] countWSNonNeg :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
countWSNonNegProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
countWSNonNegProof = do
   tsPos <- recall treeSizePosProof

   sInduct "countWSNonNeg"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) ->
           countWS w s t .>= 0)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s t -> []
         |- countWS w s t .>= (0 :: SInteger)
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> countWS w s l + countWS w s r .>= (0 :: SInteger)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                       ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                       =: sTrue
                       =: qed
            |]

-- | If a (weight, symbol) pair doesn't appear in the tree, its depth sum is zero:
-- @countWS w s t == 0 => depthSum w s t == 0@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) depthSumZeroProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: countWSNonNeg                              Q.E.D.
-- Inductive lemma (strong): depthSumZero
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, depthSum, treeSize
-- [Proven] depthSumZero :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
depthSumZeroProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
depthSumZeroProof = do
   tsPos         <- recall treeSizePosProof
   countWSNonNeg <- recall countWSNonNegProof

   sInduct "depthSumZero"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) ->
           countWS w s t .== 0 .=> depthSum w s t .== 0)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s t -> [countWS w s t .== 0]
         |- depthSum w s t .== (0 :: SInteger)
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> depthSum w s l + countWS w s l + depthSum w s r + countWS w s r .== (0 :: SInteger)
                       ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                       ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                       ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                       =: sTrue
                       =: qed
            |]

-- | The deepest leaf always appears at least once in the tree:
-- @countWS (deepW t) (deepS t) t >= 1@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) deepCountWSProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: countWSNonNeg                              Q.E.D.
-- Inductive lemma (strong): deepCountWS
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, deepS, deepW, height, treeSize
-- [Proven] deepCountWS :: Ɐt ∷ HTree → Bool
deepCountWSProof :: TP (Proof (Forall "t" HTree -> SBool))
deepCountWSProof = do
   tsPos         <- recall treeSizePosProof
   countWSNonNeg <- recall countWSNonNegProof

   sInduct "deepCountWS"
       (\(Forall @"t" t) -> countWS (deepW t) (deepS t) t .>= 1)
       (treeSize, [proofOf tsPos]) $
       \ih t -> []
         |- countWS (deepW t) (deepS t) t .>= (1 :: SInteger)
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> countWS (deepW t) (deepS t) t .>= (1 :: SInteger)
                       =: cases
                            [ height l .>= height r
                                ==> countWS (deepW t) (deepS t) t .>= (1 :: SInteger)
                                 ?? ih            `at` Inst @"t" l
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"t" r)
                                 ?? tsPos         `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> countWS (deepW t) (deepS t) t .>= (1 :: SInteger)
                                 ?? ih            `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? tsPos         `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            ]
            |]


-- | Tree height is non-negative: @height t >= 0@.
--
-- >>> runTPWith cvc5 heightNonNegProof
-- Lemma: heightNonNeg                     Q.E.D.
-- Functions proven terminating: height
-- [Proven] heightNonNeg :: Ɐt ∷ HTree → Bool
heightNonNegProof :: TP (Proof (Forall "t" HTree -> SBool))
heightNonNegProof = inductiveLemma "heightNonNeg"
    (\(Forall @"t" t) -> height t .>= 0) []

-- | The deepest leaf is always a member of the tree.
--
-- >>> runTPWith cvc5 deepMemberProof
-- Lemma: deepMember                       Q.E.D.
-- Functions proven terminating: deepS, height, member
-- [Proven] deepMember :: Ɐt ∷ HTree → Bool
deepMemberProof :: TP (Proof (Forall "t" HTree -> SBool))
deepMemberProof = inductiveLemma "deepMember"
    (\(Forall @"t" t) -> member (deepS t) t) []

-- | @max(a, b) >= a@.
--
-- >>> runTPWith cvc5 maxGeLProof
-- Lemma: maxGeL                           Q.E.D.
-- [Proven] maxGeL :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
maxGeLProof :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
maxGeLProof = lemma "maxGeL"
    (\(Forall @"a" a) (Forall @"b" b) ->
        a .<= ite (a .>= b) a (b :: SInteger)) []

-- | @max(a, b) >= b@.
--
-- >>> runTPWith cvc5 maxGeRProof
-- Lemma: maxGeR                           Q.E.D.
-- [Proven] maxGeR :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
maxGeRProof :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
maxGeRProof = lemma "maxGeR"
    (\(Forall @"a" a) (Forall @"b" b) ->
        b .<= ite (a .>= b) a (b :: SInteger)) []

-- | @height t == 0 => depthSum w s t == 0@. A height-0 tree is a single
-- leaf, so its depthSum is always 0.
--
-- >>> runTPWith cvc5 heightZeroDepthSumProof
-- Lemma: heightNonNeg                     Q.E.D.
-- Lemma: heightZeroDepthSum
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: countWS, depthSum, height
-- [Proven] heightZeroDepthSum :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
heightZeroDepthSumProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
heightZeroDepthSumProof = do
   hNN <- recall heightNonNegProof

   calc "heightZeroDepthSum"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) ->
           height t .== 0 .=> depthSum w s t .== 0) $
       \w s t -> [height t .== 0]
              |- depthSum w s t .== (0 :: SInteger)
              =: [pCase| t of
                    Tip _ _ -> trivial
                    Bin l r -> depthSum w s t .== (0 :: SInteger)
                            ?? hNN `at` Inst @"t" l
                            ?? hNN `at` Inst @"t" r
                            =: sTrue
                            =: qed
                 |]

-- | @countWS@ distributes over @Bin@: the count in a binary node equals the
-- sum of counts in its children.
--
-- >>> runTPWith cvc5 countWSBinProof
-- Lemma: countWSBin                       Q.E.D.
-- Functions proven terminating: countWS
-- [Proven] countWSBin :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐl ∷ HTree → Ɐr ∷ HTree → Bool
countWSBinProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "l" HTree -> Forall "r" HTree -> SBool))
countWSBinProof = inductiveLemma "countWSBin"
    (\(Forall @"w" w) (Forall @"s" s) (Forall @"l" l) (Forall @"r" r) ->
        countWS w s l + countWS w s r .== countWS w s (sBin l r)) []

-- | The depth of any member symbol is bounded by the tree height:
-- @member s t => depth s t <= height t@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) depthLeqHeightProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: maxGeL                                     Q.E.D.
-- Lemma: maxGeR                                     Q.E.D.
-- Inductive lemma (strong): depthLeqHeight
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: depth, height, member, treeSize
-- [Proven] depthLeqHeight :: Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
depthLeqHeightProof :: TP (Proof (Forall "s" Integer -> Forall "t" HTree -> SBool))
depthLeqHeightProof = do
   tsPos  <- recall treeSizePosProof
   maxGeL <- recall maxGeLProof
   maxGeR <- recall maxGeRProof

   sInduct "depthLeqHeight"
       (\(Forall @"s" s) (Forall @"t" t) ->
           member s t .=> depth s t .<= height t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih s t -> [member s t]
         |- depth s t .<= height t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> depth s t .<= height t
                       =: cases
                            [ member s l
                                ==> 1 + depth s l .<= 1 + ite (height l .>= height r) (height l) (height r)
                                 ?? tsPos `at` Inst @"t" r
                                 ?? ih `at` (Inst @"s" s, Inst @"t" l)
                                 ?? maxGeL `at` (Inst @"a" (height l), Inst @"b" (height r))
                                 =: sTrue
                                 =: qed
                            , sNot (member s l)
                                ==> 1 + depth s r .<= 1 + ite (height l .>= height r) (height l) (height r)
                                 ?? tsPos `at` Inst @"t" l
                                 ?? ih `at` (Inst @"s" s, Inst @"t" r)
                                 ?? maxGeR `at` (Inst @"a" (height l), Inst @"b" (height r))
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | A unique leaf's depth sum is bounded by the tree height:
-- @countWS w s t == 1 => depthSum w s t <= height t@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) depthSumLeqHeightProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: countWSNonNeg                              Q.E.D.
-- Lemma: depthSumZero                               Q.E.D.
-- Lemma: maxGeL                                     Q.E.D.
-- Lemma: maxGeR                                     Q.E.D.
-- Lemma: countWSBin                                 Q.E.D.
-- Inductive lemma (strong): depthSumLeqHeight
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.3.1                             Q.E.D.
--       Step: 1.2.2.3.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, depthSum, height, treeSize
-- [Proven] depthSumLeqHeight :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
depthSumLeqHeightProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
depthSumLeqHeightProof = do
   tsPos         <- recall treeSizePosProof
   countWSNonNeg <- recall countWSNonNegProof
   depthSumZero  <- recall depthSumZeroProof
   maxGeL        <- recall maxGeLProof
   maxGeR        <- recall maxGeRProof
   cwsBin        <- recall countWSBinProof

   sInduct "depthSumLeqHeight"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) ->
           countWS w s t .== 1 .=> depthSum w s t .<= height t)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s t -> [countWS w s t .== 1]
         |- depthSum w s t .<= height t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> depthSum w s t .<= height t
                       =: cases
                            [ countWS w s l .== 1
                                ==> depthSum w s t .<= height t
                                 ?? depthSumZero  `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                                 ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                                 ?? tsPos         `at` Inst @"t" r
                                 ?? ih            `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                                 ?? maxGeL        `at` (Inst @"a" (height l), Inst @"b" (height r))
                                 =: sTrue
                                 =: qed
                            , countWS w s l .== 0
                                ==> depthSum w s t .<= height t
                                 ?? depthSumZero  `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                                 ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                                 ?? tsPos         `at` Inst @"t" l
                                 ?? ih            `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                                 ?? maxGeR        `at` (Inst @"a" (height l), Inst @"b" (height r))
                                 =: sTrue
                                 =: qed
                            , sNot (countWS w s l .== 1) .&& sNot (countWS w s l .== 0)
                                ==> depthSum w s t .<= height t
                                 ?? cwsBin        `at` (Inst @"w" w, Inst @"s" s, Inst @"l" l, Inst @"r" r)
                                 ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                                 ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | The deepest leaf's depthSum equals the height (when unique).
--
-- >>> runTPWith (tpRibbon 50 cvc5) deepDepthSumProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: countWSNonNeg                              Q.E.D.
-- Lemma: depthSumZero                               Q.E.D.
-- Lemma: deepCountWS                                Q.E.D.
-- Lemma: countWSBin                                 Q.E.D.
-- Inductive lemma (strong): deepDepthSum
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, deepS, deepW, depthSum, height, treeSize
-- [Proven] deepDepthSum :: Ɐt ∷ HTree → Bool
deepDepthSumProof :: TP (Proof (Forall "t" HTree -> SBool))
deepDepthSumProof = do
   tsPos         <- recall treeSizePosProof
   countWSNonNeg <- recall countWSNonNegProof
   depthSumZero  <- recall depthSumZeroProof
   deepCountWS   <- recall deepCountWSProof
   cwsBin        <- recall countWSBinProof

   sInduct "deepDepthSum"
       (\(Forall @"t" t) ->
           countWS (deepW t) (deepS t) t .== 1
             .=> depthSum (deepW t) (deepS t) t .== height t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [countWS (deepW t) (deepS t) t .== 1]
         |- depthSum (deepW t) (deepS t) t .== height t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> depthSum (deepW t) (deepS t) t .== height t
                       =: cases
                            [ height l .>= height r
                                ==> depthSum (deepW t) (deepS t) t .== height t
                                 ?? cwsBin        `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"l" l, Inst @"r" r)
                                 ?? deepCountWS   `at` Inst @"t" l
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"t" r)
                                 ?? depthSumZero  `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"t" r)
                                 ?? ih            `at` Inst @"t" l
                                 ?? tsPos         `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> depthSum (deepW t) (deepS t) t .== height t
                                 ?? cwsBin        `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"l" l, Inst @"r" r)
                                 ?? deepCountWS   `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? depthSumZero  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? ih            `at` Inst @"t" r
                                 ?? tsPos         `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | First greedy swap: a leaf lighter than the deepest can be swapped
-- to the deepest position without increasing cost.
--
-- >>> runTPWith (tpRibbon 50 cvc5) greedySwap1Proof
-- Lemma: swapReducesCost                            Q.E.D.
-- Lemma: deepDepthSum                               Q.E.D.
-- Lemma: depthSumLeqHeight                          Q.E.D.
-- Lemma: greedySwap1
--   Step: 1                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: cost, countWS, deepS, deepW, depthSum, height, swap, treeSize, treeWeight
-- [Proven] greedySwap1 :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐt ∷ HTree → Bool
greedySwap1Proof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "t" HTree -> SBool))
greedySwap1Proof = do
   swpRC         <- recall swapReducesCost
   deepDepthSum  <- recall deepDepthSumProof
   depthSumLeqHt <- recall depthSumLeqHeightProof

   calc "greedySwap1"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"t" t) ->
           wa .<= deepW t
           .&& countWS wa sa t .== 1
           .&& countWS (deepW t) (deepS t) t .== 1
             .=> cost (swap wa sa (deepW t) (deepS t) t) .<= cost t) $
       \wa sa t -> [wa .<= deepW t, countWS wa sa t .== 1, countWS (deepW t) (deepS t) t .== 1]
         |- cost (swap wa sa (deepW t) (deepS t) t) .<= cost t
         ?? swpRC         `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" t)
         ?? deepDepthSum  `at` Inst @"t" t
         ?? depthSumLeqHt `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
         =: sTrue
         =: qed

-- | Second greedy swap: a leaf lighter than the sibling can be swapped
-- to the sibling position without increasing cost.
--
-- >>> runTPWith (tpRibbon 50 cvc5) greedySwap2Proof
-- Lemma: swapReducesCost                            Q.E.D.
-- Lemma: sibDepthSum                                Q.E.D.
-- Lemma: depthSumLeqHeight                          Q.E.D.
-- Lemma: greedySwap2
--   Step: 1                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: cost, countWS, deepS, deepW, depthSum, height, sibS, sibW, swap, treeSize, treeWeight
-- [Proven] greedySwap2 :: Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
greedySwap2Proof :: TP (Proof (Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
greedySwap2Proof = do
   swpRC         <- recall swapReducesCost
   sibDepthSum   <- recall sibDepthSumProof
   depthSumLeqHt <- recall depthSumLeqHeightProof

   calc "greedySwap2"
       (\(Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           wb .<= sibW t
           .&& countWS wb sb t .== 1
           .&& countWS (sibW t) (sibS t) t .== 1
             .=> cost (swap wb sb (sibW t) (sibS t) t) .<= cost t) $
       \wb sb t -> [wb .<= sibW t, countWS wb sb t .== 1, countWS (sibW t) (sibS t) t .== 1]
         |- cost (swap wb sb (sibW t) (sibS t) t) .<= cost t
         ?? swpRC         `at` (Inst @"wa" wb, Inst @"sa" sb, Inst @"wb" (sibW t), Inst @"sb" (sibS t), Inst @"t" t)
         ?? sibDepthSum   `at` Inst @"t" t
         ?? depthSumLeqHt `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
         =: sTrue
         =: qed

-- | Combined greedy choice: apply two swaps to place the two lightest leaves at the
-- deepest and sibling positions without increasing cost.  The first swap moves
-- @(wa, sa)@ to the deepest leaf; the second moves @(wb, sb)@ to its sibling.
-- Conditions on the intermediate tree @t1 = swap wa sa (deepW t) (deepS t) t@ are
-- stated directly as preconditions.
--
-- >>> runTPWith (tpRibbon 50 cvc5) greedyChoiceProof
-- Lemma: greedySwap1                                Q.E.D.
-- Lemma: greedySwap2                                Q.E.D.
-- Lemma: greedyChoice
--   Step: 1                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: cost, countWS, deepS, deepW, depthSum, height, sibS, sibW, swap, treeSize, treeWeight
-- [Proven] greedyChoice :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
greedyChoiceProof :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                                -> Forall "wb" Integer -> Forall "sb" Integer
                                -> Forall "t"  HTree   -> SBool))
greedyChoiceProof = do
   gs1 <- recall greedySwap1Proof
   gs2 <- recall greedySwap2Proof

   calc "greedyChoice"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           let t1 = swap wa sa (deepW t) (deepS t) t
           in    wa .<= deepW t
             .&& countWS wa sa t .== 1
             .&& countWS (deepW t) (deepS t) t .== 1
             .&& wb .<= sibW t1
             .&& countWS wb sb t1 .== 1
             .&& countWS (sibW t1) (sibS t1) t1 .== 1
               .=> cost (swap wb sb (sibW t1) (sibS t1) t1) .<= cost t) $
       \wa sa wb sb t ->
           let t1 = swap wa sa (deepW t) (deepS t) t
           in [ wa .<= deepW t
              , countWS wa sa t .== 1
              , countWS (deepW t) (deepS t) t .== 1
              , wb .<= sibW t1
              , countWS wb sb t1 .== 1
              , countWS (sibW t1) (sibS t1) t1 .== 1
              ]
           |- cost (swap wb sb (sibW t1) (sibS t1) t1) .<= cost t
           ?? gs1 `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" t)
           ?? gs2 `at` (Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t1)
           =: sTrue
           =: qed

-- ** Swap structural invariants
--
-- Swapping two leaves preserves tree structure: height, @countWS@ and @depthSum@
-- for unrelated pairs, and exchanges them for the swapped pairs.

-- | Swap preserves tree height: @height (swap wa sa wb sb t) == height t@.
-- Since swap only relabels leaves without changing the Tip\/Bin skeleton,
-- the height is invariant.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapPreservesHeightProof
-- Lemma: treeSizePos                                Q.E.D.
-- Inductive lemma (strong): swapPreservesHeight
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: height, swap, treeSize
-- [Proven] swapPreservesHeight :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapPreservesHeightProof :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                                       -> Forall "wb" Integer -> Forall "sb" Integer
                                       -> Forall "t"  HTree   -> SBool))
swapPreservesHeightProof = do
   tsPos <- recall treeSizePosProof

   sInduct "swapPreservesHeight"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           height (swap wa sa wb sb t) .== height t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> []
         |- height (swap wa sa wb sb t) .== height t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> height (swap wa sa wb sb t) .== height t
                       ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- | Swapping @(wa, sa)@ with the deepest leaf places @wa@ at the deepest position:
-- @deepW (swap wa sa (deepW t) (deepS t) t) == wa@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapDeepWProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: swapPreservesHeight                        Q.E.D.
-- Inductive lemma (strong): swapDeepW
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: deepS, deepW, height, swap, treeSize
-- [Proven] swapDeepW :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐt ∷ HTree → Bool
swapDeepWProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "t" HTree -> SBool))
swapDeepWProof = do
   tsPos <- recall treeSizePosProof
   swpHt <- recall swapPreservesHeightProof

   sInduct "swapDeepW"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"t" t) ->
           deepW (swap wa sa (deepW t) (deepS t) t) .== wa)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa t -> []
         |- deepW (swap wa sa (deepW t) (deepS t) t) .== wa
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> deepW (swap wa sa (deepW t) (deepS t) t) .== wa
                       =: cases
                            [ height l .>= height r
                                ==> deepW (swap wa sa (deepW t) (deepS t) t) .== wa
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" l)
                                 ?? tsPos `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> deepW (swap wa sa (deepW t) (deepS t) t) .== wa
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" r)
                                 ?? tsPos `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | Swapping @(wa, sa)@ with the deepest leaf places @sa@ at the deepest position:
-- @deepS (swap wa sa (deepW t) (deepS t) t) == sa@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapDeepSProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: swapPreservesHeight                        Q.E.D.
-- Inductive lemma (strong): swapDeepS
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: deepS, deepW, height, swap, treeSize
-- [Proven] swapDeepS :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐt ∷ HTree → Bool
swapDeepSProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "t" HTree -> SBool))
swapDeepSProof = do
   tsPos <- recall treeSizePosProof
   swpHt <- recall swapPreservesHeightProof

   sInduct "swapDeepS"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"t" t) ->
           deepS (swap wa sa (deepW t) (deepS t) t) .== sa)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa t -> []
         |- deepS (swap wa sa (deepW t) (deepS t) t) .== sa
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> deepS (swap wa sa (deepW t) (deepS t) t) .== sa
                       =: cases
                            [ height l .>= height r
                                ==> deepS (swap wa sa (deepW t) (deepS t) t) .== sa
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" l)
                                 ?? tsPos `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> deepS (swap wa sa (deepW t) (deepS t) t) .== sa
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" r)
                                 ?? tsPos `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | Swap preserves countWS for unrelated (weight, symbol) pairs.
-- Uses tuples to keep the arity within sInduct's limit.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapPreservesCountWSProof
-- Lemma: treeSizePos                                Q.E.D.
-- Inductive lemma (strong): swapPreservesCountWS
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, swap, treeSize
-- [Proven] swapPreservesCountWS :: Ɐa ∷ (Integer, Integer) → Ɐb ∷ (Integer, Integer) → Ɐc ∷ (Integer, Integer) → Ɐt ∷ HTree → Bool
swapPreservesCountWSProof :: TP (Proof (   Forall "a" (Integer, Integer)
                                        -> Forall "b" (Integer, Integer)
                                        -> Forall "c" (Integer, Integer)
                                        -> Forall "t" HTree -> SBool))
swapPreservesCountWSProof = do
   tsPos <- recall treeSizePosProof

   sInduct "swapPreservesCountWS"
       (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"t" t) ->
           let (wa, sa) = untuple a
               (wb, sb) = untuple b
               (w, s)   = untuple c
           in sNot (w .== wa .&& s .== sa) .&& sNot (w .== wb .&& s .== sb)
              .=> countWS w s (swap wa sa wb sb t) .== countWS w s t)
       (\_ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih a b c t ->
         let (wa, sa) = untuple a
             (wb, sb) = untuple b
             (w, s)   = untuple c
         in [sNot (w .== wa .&& s .== sa), sNot (w .== wb .&& s .== sb)]
           |- countWS w s (swap wa sa wb sb t) .== countWS w s t
           =: [pCase| t of
                 Tip _ _ -> trivial
                 Bin l r -> countWS w s (swap wa sa wb sb t) .== countWS w s t
                         ?? ih `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" l)
                         ?? ih `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" r)
                         ?? tsPos `at` Inst @"t" l
                         ?? tsPos `at` Inst @"t" r
                         =: sTrue
                         =: qed
              |]

-- | Swap preserves depthSum for unrelated (weight, symbol) pairs.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapPreservesDepthSumProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: swapPreservesCountWS                       Q.E.D.
-- Inductive lemma (strong): swapPreservesDepthSum
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, depthSum, swap, treeSize
-- [Proven] swapPreservesDepthSum :: Ɐa ∷ (Integer, Integer) → Ɐb ∷ (Integer, Integer) → Ɐc ∷ (Integer, Integer) → Ɐt ∷ HTree → Bool
swapPreservesDepthSumProof :: TP (Proof (   Forall "a" (Integer, Integer)
                                          -> Forall "b" (Integer, Integer)
                                          -> Forall "c" (Integer, Integer)
                                          -> Forall "t" HTree -> SBool))
swapPreservesDepthSumProof = do
   tsPos   <- recall treeSizePosProof
   swapCWS <- recall swapPreservesCountWSProof

   sInduct "swapPreservesDepthSum"
       (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"t" t) ->
           let (wa, sa) = untuple a
               (wb, sb) = untuple b
               (w, s)   = untuple c
           in sNot (w .== wa .&& s .== sa) .&& sNot (w .== wb .&& s .== sb)
              .=> depthSum w s (swap wa sa wb sb t) .== depthSum w s t)
       (\_ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih a b c t ->
         let (wa, sa) = untuple a
             (wb, sb) = untuple b
             (w, s)   = untuple c
         in [sNot (w .== wa .&& s .== sa), sNot (w .== wb .&& s .== sb)]
           |- depthSum w s (swap wa sa wb sb t) .== depthSum w s t
           =: [pCase| t of
                 Tip _ _ -> trivial
                 Bin l r -> depthSum w s (swap wa sa wb sb t) .== depthSum w s t
                         ?? ih      `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" l)
                         ?? ih      `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" r)
                         ?? swapCWS `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" l)
                         ?? swapCWS `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" r)
                         ?? tsPos   `at` Inst @"t" l
                         ?? tsPos   `at` Inst @"t" r
                         =: sTrue
                         =: qed
              |]

-- | Swap exchanges countWS: after swapping @(wa,sa)@ with @(wb,sb)@,
-- the count of @(wb,sb)@ equals the old count of @(wa,sa)@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapExchangesCountWSProof
-- Lemma: treeSizePos                                Q.E.D.
-- Inductive lemma (strong): swapExchangesCountWS
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, swap, treeSize
-- [Proven] swapExchangesCountWS :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapExchangesCountWSProof :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                                        -> Forall "wb" Integer -> Forall "sb" Integer
                                        -> Forall "t"  HTree   -> SBool))
swapExchangesCountWSProof = do
   tsPos <- recall treeSizePosProof

   sInduct "swapExchangesCountWS"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb)
        (Forall @"t" t) ->
           countWS wb sb (swap wa sa wb sb t) .== countWS wa sa t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> []
         |- countWS wb sb (swap wa sa wb sb t) .== countWS wa sa t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> countWS wb sb (swap wa sa wb sb t) .== countWS wa sa t
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- | Swap exchanges depthSum: after swapping, the depthSum of @(wb,sb)@
-- equals the old depthSum of @(wa,sa)@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) swapExchangesDepthSumProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: swapExchangesCountWS                       Q.E.D.
-- Inductive lemma (strong): swapExchangesDepthSum
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, depthSum, swap, treeSize
-- [Proven] swapExchangesDepthSum :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapExchangesDepthSumProof :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                                          -> Forall "wb" Integer -> Forall "sb" Integer
                                          -> Forall "t"  HTree   -> SBool))
swapExchangesDepthSumProof = do
   tsPos    <- recall treeSizePosProof
   swapXCWS <- recall swapExchangesCountWSProof

   sInduct "swapExchangesDepthSum"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb)
        (Forall @"t" t) ->
           depthSum wb sb (swap wa sa wb sb t) .== depthSum wa sa t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> []
         |- depthSum wb sb (swap wa sa wb sb t) .== depthSum wa sa t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> depthSum wb sb (swap wa sa wb sb t) .== depthSum wa sa t
                       ?? ih       `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih       `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? swapXCWS `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? swapXCWS `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? tsPos    `at` Inst @"t" l
                       ?? tsPos    `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- ** Sibling lemmas
--
-- The sibling of the deepest leaf has count at least 1,
-- and its depthSum equals the height when it is unique.

-- | The sibling leaf is counted at least once.
--
-- >>> runTPWith (tpRibbon 50 cvc5) sibCountWSProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: countWSNonNeg                              Q.E.D.
-- Lemma: deepCountWS                                Q.E.D.
-- Lemma: heightNonNeg                               Q.E.D.
-- Inductive lemma (strong): sibCountWS
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.3.1                             Q.E.D.
--       Step: 1.2.2.3.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, deepS, deepW, height, sibS, sibW, treeSize
-- [Proven] sibCountWS :: Ɐt ∷ HTree → Bool
sibCountWSProof :: TP (Proof (Forall "t" HTree -> SBool))
sibCountWSProof = do
   tsPos         <- recall treeSizePosProof
   countWSNonNeg <- recall countWSNonNegProof
   deepCountWS   <- recall deepCountWSProof
   heightNonNeg  <- recall heightNonNegProof

   sInduct "sibCountWS"
       (\(Forall @"t" t) -> countWS (sibW t) (sibS t) t .>= 1)
       (treeSize, [proofOf tsPos]) $
       \ih t -> []
         |- countWS (sibW t) (sibS t) t .>= (1 :: SInteger)
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> countWS (sibW t) (sibS t) t .>= (1 :: SInteger)
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> countWS (sibW t) (sibS t) t .>= (1 :: SInteger)
                                 ?? deepCountWS   `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 =: sTrue
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> countWS (sibW t) (sibS t) t .>= (1 :: SInteger)
                                 ?? ih            `at` Inst @"t" l
                                 ?? countWSNonNeg `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"t" r)
                                 ?? tsPos         `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> countWS (sibW t) (sibS t) t .>= (1 :: SInteger)
                                 ?? ih            `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"t" l)
                                 ?? tsPos         `at` Inst @"t" l
                                 ?? heightNonNeg  `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | The sibling leaf's depthSum equals the height (when unique).
--
-- >>> runTPWith (tpRibbon 50 cvc5) sibDepthSumProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: countWSNonNeg                              Q.E.D.
-- Lemma: depthSumZero                               Q.E.D.
-- Lemma: deepCountWS                                Q.E.D.
-- Lemma: heightNonNeg                               Q.E.D.
-- Lemma: sibCountWS                                 Q.E.D.
-- Lemma: countWSBin                                 Q.E.D.
-- Lemma: heightZeroDepthSum                         Q.E.D.
-- Inductive lemma (strong): sibDepthSum
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.3.1                             Q.E.D.
--       Step: 1.2.2.3.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: countWS, deepS, deepW, depthSum, height, sibS, sibW, treeSize
-- [Proven] sibDepthSum :: Ɐt ∷ HTree → Bool
sibDepthSumProof :: TP (Proof (Forall "t" HTree -> SBool))
sibDepthSumProof = do
   tsPos         <- recall treeSizePosProof
   countWSNonNeg <- recall countWSNonNegProof
   depthSumZero  <- recall depthSumZeroProof
   deepCountWS   <- recall deepCountWSProof
   heightNonNeg  <- recall heightNonNegProof
   sibCountWS    <- recall sibCountWSProof
   cwsBin        <- recall countWSBinProof
   heightZeroDS  <- recall heightZeroDepthSumProof

   sInduct "sibDepthSum"
       (\(Forall @"t" t) ->
           countWS (sibW t) (sibS t) t .== 1
             .=> depthSum (sibW t) (sibS t) t .== height t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [countWS (sibW t) (sibS t) t .== 1]
         |- depthSum (sibW t) (sibS t) t .== height t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> depthSum (sibW t) (sibS t) t .== height t
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> depthSum (sibW t) (sibS t) t .== height t
                                 ?? cwsBin        `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"l" l, Inst @"r" r)
                                 ?? deepCountWS   `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? depthSumZero  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? heightNonNeg  `at` Inst @"t" r
                                 ?? heightZeroDS  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? heightZeroDS  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" r)
                                 =: sTrue
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> depthSum (sibW t) (sibS t) t .== height t
                                 ?? cwsBin        `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"l" l, Inst @"r" r)
                                 ?? sibCountWS    `at` Inst @"t" l
                                 ?? countWSNonNeg `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"t" r)
                                 ?? depthSumZero  `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"t" r)
                                 ?? ih            `at` Inst @"t" l
                                 ?? tsPos         `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> depthSum (sibW t) (sibS t) t .== height t
                                 ?? cwsBin        `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"l" l, Inst @"r" r)
                                 ?? sibCountWS    `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"t" l)
                                 ?? depthSumZero  `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"t" l)
                                 ?? ih            `at` Inst @"t" r
                                 ?? tsPos         `at` Inst @"t" l
                                 ?? heightNonNeg  `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- ** Tree collapse and cost decomposition
--
-- Collapsing the deepest sibling pair into a single leaf preserves
-- 'treeWeight' and decomposes 'cost' into the collapsed cost plus
-- the weights of the two merged leaves.

-- | Collapse the deepest sibling pair: replace the 'Bin' node whose children
-- are both tips (at maximum depth) with a single 'Tip' whose weight is their sum.
-- The symbol of the collapsed leaf is 0 (irrelevant for cost calculations).
collapse :: SHTree -> SHTree
collapse = smtFunction "collapse"
         $ \t -> [sCase| t of
                    Tip w s -> sTip w s
                    Bin l r | height l .>= height r .&& height l .== 0
                                -> sTip (treeWeight l + treeWeight r) 0
                            | height l .>= height r
                                -> sBin (collapse l) r
                            | height r .== 0
                                -> sTip (treeWeight l + treeWeight r) 0
                            | True
                                -> sBin l (collapse r)
                 |]

-- | Collapsing preserves tree weight: @treeWeight (collapse t) == treeWeight t@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) collapsePreservesWeightProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: heightNonNeg                               Q.E.D.
-- Inductive lemma (strong): collapsePreservesWeight
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.3.1                             Q.E.D.
--       Step: 1.2.2.3.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: collapse, height, treeSize, treeWeight
-- [Proven] collapsePreservesWeight :: Ɐt ∷ HTree → Bool
collapsePreservesWeightProof :: TP (Proof (Forall "t" HTree -> SBool))
collapsePreservesWeightProof = do
   tsPos <- recall treeSizePosProof
   hNN   <- recall heightNonNegProof

   sInduct "collapsePreservesWeight"
       (\(Forall @"t" t) -> treeWeight (collapse t) .== treeWeight t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> []
         |- treeWeight (collapse t) .== treeWeight t
         =: [pCase| t of
               Tip _ _ -> trivial
               Bin l r -> treeWeight (collapse t) .== treeWeight t
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> treeWeight (collapse t) .== treeWeight t
                                 =: sTrue
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> treeWeight (collapse t) .== treeWeight t
                                 ?? ih `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> treeWeight (collapse t) .== treeWeight t
                                 ?? ih `at` Inst @"t" r
                                 ?? tsPos `at` Inst @"t" l
                                 ?? hNN `at` Inst @"t" l
                                 ?? hNN `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- | Trees with positive height have at least 3 nodes (they must be a 'Bin'
-- with two children, each of size at least 1).
--
-- >>> runTPWith cvc5 heightPosTreeSizeProof
-- Lemma: treeSizePos                      Q.E.D.
-- Lemma: heightPosTreeSize                Q.E.D.
-- Functions proven terminating: height, treeSize
-- [Proven] heightPosTreeSize :: Ɐt ∷ HTree → Bool
heightPosTreeSizeProof :: TP (Proof (Forall "t" HTree -> SBool))
heightPosTreeSizeProof = do
   tsPos <- recall treeSizePosProof
   lemma "heightPosTreeSize"
       (\(Forall @"t" t) -> height t .>= 1 .=> treeSize t .>= 3)
       [proofOf tsPos]

-- | Cost decomposition: the cost of a tree with at least two leaves equals
-- the cost of its collapse plus the weights of the deepest sibling pair.
-- @cost t == cost (collapse t) + deepW t + sibW t@ when @treeSize t >= 2@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) costDecompProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: collapsePreservesWeight                    Q.E.D.
-- Cached: heightNonNeg                              Q.E.D.
-- Lemma: heightPosTreeSize                          Q.E.D.
-- Inductive lemma (strong): costDecomp
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                   Q.E.D.
--     Step: 1.1.2                                   Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2 (2 way case split)
--         Step: 1.2.2.1.2.1.1                       Q.E.D.
--         Step: 1.2.2.1.2.1.2                       Q.E.D.
--         Step: 1.2.2.1.2.2.1                       Q.E.D.
--         Step: 1.2.2.1.2.2.2 (2 way case split)
--           Step: 1.2.2.1.2.2.2.1.1                 Q.E.D.
--           Step: 1.2.2.1.2.2.2.1.2                 Q.E.D.
--           Step: 1.2.2.1.2.2.2.2.1                 Q.E.D.
--           Step: 1.2.2.1.2.2.2.2.2                 Q.E.D.
--           Step: 1.2.2.1.2.2.2.Completeness        Q.E.D.
--         Step: 1.2.2.1.2.Completeness              Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2 (2 way case split)
--         Step: 1.2.2.2.2.1.1                       Q.E.D.
--         Step: 1.2.2.2.2.1.2 (2 way case split)
--           Step: 1.2.2.2.2.1.2.1.1                 Q.E.D.
--           Step: 1.2.2.2.2.1.2.1.2                 Q.E.D.
--           Step: 1.2.2.2.2.1.2.2.1                 Q.E.D.
--           Step: 1.2.2.2.2.1.2.2.2                 Q.E.D.
--           Step: 1.2.2.2.2.1.2.Completeness        Q.E.D.
--         Step: 1.2.2.2.2.2.1                       Q.E.D.
--         Step: 1.2.2.2.2.2.2                       Q.E.D.
--         Step: 1.2.2.2.2.Completeness              Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: collapse, cost, deepW, height, sibW, treeSize, treeWeight
-- [Proven] costDecomp :: Ɐt ∷ HTree → Bool
costDecompProof :: TP (Proof (Forall "t" HTree -> SBool))
costDecompProof = do
   tsPos    <- recall treeSizePosProof
   collWt   <- recall collapsePreservesWeightProof
   hNN      <- recall heightNonNegProof
   hpTS     <- recall heightPosTreeSizeProof

   sInduct "costDecomp"
       (\(Forall @"t" t) ->
           treeSize t .>= 2 .=> cost t .== cost (collapse t) + deepW t + sibW t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [treeSize t .>= 2]
         |- cost t .== cost (collapse t) + deepW t + sibW t
         =: [pCase| t of
               Tip _ _ -> cost t .== cost (collapse t) + deepW t + sibW t
                       =: sTrue
                       =: qed
               Bin l r -> cost t .== cost (collapse t) + deepW t + sibW t
                       =: case l of
                            Tip _ _ -> cost t .== cost (collapse t) + deepW t + sibW t
                                    =: case r of
                                         Tip _ _ -> cost t .== cost (collapse t) + deepW t + sibW t
                                                 =: sTrue
                                                 =: qed
                                         Bin rl rr -> cost t .== cost (collapse t) + deepW t + sibW t
                                                  =: cases
                                                       [ height l .>= height r
                                                           ==> cost t .== cost (collapse t) + deepW t + sibW t
                                                            ?? hNN `at` Inst @"t" rl
                                                            ?? hNN `at` Inst @"t" rr
                                                            =: sTrue
                                                            =: qed
                                                       , sNot (height l .>= height r)
                                                           ==> cost t .== cost (collapse t) + deepW t + sibW t
                                                            ?? ih     `at` Inst @"t" r
                                                            ?? tsPos  `at` Inst @"t" l
                                                            ?? collWt `at` Inst @"t" r
                                                            ?? hpTS   `at` Inst @"t" r
                                                            =: sTrue
                                                            =: qed
                                                       ]
                            Bin ll lr -> cost t .== cost (collapse t) + deepW t + sibW t
                                    =: cases
                                         [ height l .>= height r
                                             ==> cost t .== cost (collapse t) + deepW t + sibW t
                                              =: cases
                                                   [ height l .== 0
                                                       ==> cost t .== cost (collapse t) + deepW t + sibW t
                                                        ?? hNN `at` Inst @"t" ll
                                                        ?? hNN `at` Inst @"t" lr
                                                        =: sTrue
                                                        =: qed
                                                   , sNot (height l .== 0)
                                                       ==> cost t .== cost (collapse t) + deepW t + sibW t
                                                        ?? ih     `at` Inst @"t" l
                                                        ?? tsPos  `at` Inst @"t" r
                                                        ?? collWt `at` Inst @"t" l
                                                        ?? hpTS   `at` Inst @"t" l
                                                        ?? hNN    `at` Inst @"t" l
                                                        =: sTrue
                                                        =: qed
                                                   ]
                                         , sNot (height l .>= height r)
                                             ==> cost t .== cost (collapse t) + deepW t + sibW t
                                              ?? ih     `at` Inst @"t" r
                                              ?? tsPos  `at` Inst @"t" l
                                              ?? collWt `at` Inst @"t" r
                                              ?? hpTS   `at` Inst @"t" r
                                              ?? hNN    `at` Inst @"t" l
                                              ?? hNN    `at` Inst @"t" r
                                              =: sTrue
                                              =: qed
                                         ]
            |]

-- | Height zero means the tree is a single leaf (treeSize 1).
--
-- >>> runTPWith cvc5 heightZeroTreeSizeOneProof
-- Lemma: heightNonNeg                     Q.E.D.
-- Lemma: heightZeroTreeSizeOne            Q.E.D.
-- Functions proven terminating: height, treeSize
-- [Proven] heightZeroTreeSizeOne :: Ɐt ∷ HTree → Bool
heightZeroTreeSizeOneProof :: TP (Proof (Forall "t" HTree -> SBool))
heightZeroTreeSizeOneProof = do
   hNN <- recall heightNonNegProof
   lemma "heightZeroTreeSizeOne"
       (\(Forall @"t" t) -> height t .== 0 .=> treeSize t .== 1)
       [proofOf hNN]

-- | Collapsing reduces tree size by exactly 2: the deepest sibling pair
-- (a @Bin@ with two @Tip@ children) is replaced by a single @Tip@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) collapseReducesTreeSizeProof
-- Lemma: treeSizePos                                Q.E.D.
-- Lemma: heightNonNeg                               Q.E.D.
-- Lemma: heightPosTreeSize                          Q.E.D.
-- Lemma: heightZeroTreeSizeOne                      Q.E.D.
-- Inductive lemma (strong): collapseReducesTreeSize
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                   Q.E.D.
--     Step: 1.1.2                                   Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                             Q.E.D.
--       Step: 1.2.2.1.2                             Q.E.D.
--       Step: 1.2.2.2.1                             Q.E.D.
--       Step: 1.2.2.2.2                             Q.E.D.
--       Step: 1.2.2.3.1                             Q.E.D.
--       Step: 1.2.2.3.2                             Q.E.D.
--       Step: 1.2.2.Completeness                    Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Functions proven terminating: collapse, height, treeSize, treeWeight
-- [Proven] collapseReducesTreeSize :: Ɐt ∷ HTree → Bool
collapseReducesTreeSizeProof :: TP (Proof (Forall "t" HTree -> SBool))
collapseReducesTreeSizeProof = do
   tsPos <- recall treeSizePosProof
   hNN   <- recall heightNonNegProof
   hpTS  <- recall heightPosTreeSizeProof
   hzTS  <- recall heightZeroTreeSizeOneProof

   sInduct "collapseReducesTreeSize"
       (\(Forall @"t" t) ->
           treeSize t .>= 2 .=> treeSize (collapse t) .== treeSize t - 2)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [treeSize t .>= 2]
         |- treeSize (collapse t) .== treeSize t - 2
         =: [pCase| t of
               Tip _ _ -> treeSize (collapse t) .== treeSize t - 2
                       =: sTrue
                       =: qed
               Bin l r -> treeSize (collapse t) .== treeSize t - 2
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> treeSize (collapse t) .== treeSize t - 2
                                 ?? hzTS `at` Inst @"t" l
                                 ?? hzTS `at` Inst @"t" r
                                 ?? hNN  `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> treeSize (collapse t) .== treeSize t - 2
                                 ?? ih    `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 ?? hpTS  `at` Inst @"t" l
                                 ?? hNN   `at` Inst @"t" l
                                 =: sTrue
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> treeSize (collapse t) .== treeSize t - 2
                                 ?? ih    `at` Inst @"t" r
                                 ?? tsPos `at` Inst @"t" l
                                 ?? hpTS  `at` Inst @"t" r
                                 ?? hNN   `at` Inst @"t" l
                                 ?? hNN   `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            ]
            |]

-- * Part 3: Huffman construction and optimality
--
-- We build the Huffman tree by greedily merging the two lightest subtrees
-- from a weight-sorted forest, then prove this construction is optimal.

-- ** Building the Huffman tree

-- | Insert a tree into a weight-sorted forest, maintaining sort order.
sortedInsert :: SHTree -> SList HTree -> SList HTree
sortedInsert = smtFunction "sortedInsert"
             $ \t ts -> [sCase| ts of
                           []                                     -> [t]
                           u : us | treeWeight t .<= treeWeight u -> t .: u .: us
                                  | True                          -> u .: sortedInsert t us
                        |]

-- | Length of forest after sorted insertion is one more than the original.
--
-- >>> runTPWith cvc5 sortedInsertLengthProof
-- Inductive lemma (strong): sortedInsertLength
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                   Q.E.D.
--       Step: 1.2.2.1.2                   Q.E.D.
--       Step: 1.2.2.2.1                   Q.E.D.
--       Step: 1.2.2.2.2                   Q.E.D.
--       Step: 1.2.2.Completeness          Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: sortedInsert, treeWeight
-- [Proven] sortedInsertLength :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertLengthProof :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertLengthProof =
   sInduct "sortedInsertLength"
       (\(Forall @"t" t) (Forall @"ts" ts) ->
           length (sortedInsert t ts) .== 1 + length ts)
       (\_ ts -> length ts, []) $
       \ih t ts -> []
         |- length (sortedInsert t ts) .== 1 + length ts
         =: [pCase| ts of
               [] -> length (sortedInsert t ts) .== 1 + length ts
                  =: sTrue
                  =: qed
               u : us -> length (sortedInsert t ts) .== 1 + length ts
                      =: cases
                           [ treeWeight t .<= treeWeight u
                               ==> length (sortedInsert t ts) .== 1 + length ts
                                =: sTrue
                                =: qed
                           , sNot (treeWeight t .<= treeWeight u)
                               ==> length (sortedInsert t ts) .== 1 + length ts
                                ?? ih `at` (Inst @"t" t, Inst @"ts" us)
                                =: sTrue
                                =: qed
                           ]
            |]

-- | Build a Huffman tree from a weight-sorted forest by repeatedly merging
-- the two lightest subtrees.
buildHuffman :: SList HTree -> SHTree
buildHuffman = smtFunctionWithMeasure "buildHuffman"
                 (length @HTree, [measureLemma sortedInsertLengthProof])
             $ \ts -> [sCase| ts of
                         []     -> sTip 0 0
                         t : rest -> case rest of
                                       []     -> t
                                       u : us -> buildHuffman (sortedInsert (sBin t u) us)
                      |]
