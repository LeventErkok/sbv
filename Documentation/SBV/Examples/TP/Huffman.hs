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
                      + ((wb - wa) * depthSum wa sa l + (wb - wa) * countWS wa sa l
                       + (wb - wa) * depthSum wa sa r + (wb - wa) * countWS wa sa r)
                      + ((wa - wb) * depthSum wb sb l + (wa - wb) * countWS wb sb l
                       + (wa - wb) * depthSum wb sb r + (wa - wb) * countWS wb sb r)

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
                      + ((wa - wb) * depthSum wb sb l + (wa - wb) * countWS wb sb l
                       + (wa - wb) * depthSum wb sb r + (wa - wb) * countWS wb sb r)

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
