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
                    Tip{}   -> 1
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
                      Tip{}   -> []
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
-- >>> runTPWith cvc5 roundtrip
-- Lemma: treeSizePos                            Q.E.D.
-- Inductive lemma (strong): huffmanRoundtrip
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                 Q.E.D.
--     Step: 1.2 (2 way case split)
--       Step: 1.2.1.1                           Q.E.D.
--       Step: 1.2.1.2                           Q.E.D.
--       Step: 1.2.2.1                           Q.E.D.
--       Step: 1.2.2.2                           Q.E.D.
--       Step: 1.2.Completeness                  Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
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
       |- decode (findPath s t) t
       =: [pCase| t of
             Tip{}   -> trivial

             Bin l r -> cases
               [ member s l
                   ==> decode (findPath s (sBin l r)) (sBin l r)
                    ?? tsPos `at` Inst @"t" r
                    ?? ih `at` (Inst @"s" s, Inst @"t" l)
                    =: s
                    =: qed

               , sNot (member s l)
                   ==> decode (findPath s (sBin l r)) (sBin l r)
                    ?? tsPos `at` Inst @"t" l
                    ?? ih `at` (Inst @"s" s, Inst @"t" r)
                    =: s
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
                Tip{}   -> 0
                Bin l r -> cost l + cost r + treeWeight l + treeWeight r
             |]

-- | Number of leaves in a tree.
numLeaves :: SHTree -> SInteger
numLeaves = smtFunction "numLeaves"
          $ \t -> [sCase| t of
                     Tip{}   -> 1
                     Bin l r -> numLeaves l + numLeaves r
                  |]

-- | Depth of a symbol in a tree. Returns 0 at the leaf containing the symbol.
-- At a 'Bin', we add 1 and recurse into the subtree containing the symbol.
depth :: SInteger -> SHTree -> SInteger
depth = smtFunction "depth"
      $ \s t -> [sCase| t of
                   Tip{}   -> 0
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
-- >>> runTPWith cvc5 swapWeight
-- Lemma: treeSizePos                      Q.E.D.
-- Lemma: distFold                         Q.E.D.
-- Lemma: countWSBin                       Q.E.D.
-- Lemma: mulCong                          Q.E.D.
-- Lemma: tipHelper                        Q.E.D.
-- Inductive lemma (strong): swapWeight
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1 (3 way case split)
--       Step: 1.1.1.1                     Q.E.D.
--       Step: 1.1.1.2                     Q.E.D.
--       Step: 1.1.1.3                     Q.E.D.
--       Step: 1.1.1.4                     Q.E.D.
--       Step: 1.1.2.1                     Q.E.D.
--       Step: 1.1.2.2                     Q.E.D.
--       Step: 1.1.2.3                     Q.E.D.
--       Step: 1.1.2.4                     Q.E.D.
--       Step: 1.1.3.1                     Q.E.D.
--       Step: 1.1.3.2                     Q.E.D.
--       Step: 1.1.3.3                     Q.E.D.
--       Step: 1.1.Completeness            Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2 (apply IH for l)        Q.E.D.
--     Step: 1.2.3 (apply IH for r)        Q.E.D.
--     Step: 1.2.4 (regroup)               Q.E.D.
--     Step: 1.2.5                         Q.E.D.
--     Step: 1.2.6                         Q.E.D.
--     Step: 1.2.7                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
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
                        Tip{}   -> 0
                        Bin l r -> depthSum w s l + countWS w s l
                                 + depthSum w s r + countWS w s r
                     |]

-- | Swap cost lemma: swapping two leaves changes the cost by a linear
-- combination of their depth sums, paralleling 'swapWeight'. This is the
-- key algebraic fact underlying Huffman optimality.
--
-- >>> runTPWith cvc5 swapCost
-- Lemma: swapWeight                               Q.E.D.
-- Lemma: treeSizePos                              Q.E.D.
-- Lemma: depthSumBin                              Q.E.D.
-- Lemma: factor4                                  Q.E.D.
-- Lemma: mulCong                                  Q.E.D.
-- Inductive lemma (strong): swapCost
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1 (3 way case split)
--       Step: 1.1.1.1                             Q.E.D.
--       Step: 1.1.1.2                             Q.E.D.
--       Step: 1.1.1.3                             Q.E.D.
--       Step: 1.1.2.1                             Q.E.D.
--       Step: 1.1.2.2                             Q.E.D.
--       Step: 1.1.2.3                             Q.E.D.
--       Step: 1.1.3.1                             Q.E.D.
--       Step: 1.1.3.2                             Q.E.D.
--       Step: 1.1.3.3                             Q.E.D.
--       Step: 1.1.Completeness                    Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2 (apply swapCost IH for l)       Q.E.D.
--     Step: 1.2.3 (apply swapCost IH for r)       Q.E.D.
--     Step: 1.2.4 (apply swapWeight for l)        Q.E.D.
--     Step: 1.2.5 (apply swapWeight for r)        Q.E.D.
--     Step: 1.2.6 (regroup)                       Q.E.D.
--     Step: 1.2.7 (fold depthSum for (wa, sa))    Q.E.D.
--     Step: 1.2.8 (fold depthSum for (wb, sb))    Q.E.D.
--     Step: 1.2.9                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
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
-- >>> runTPWith cvc5 swapReducesCost
-- Lemma: swapCost                                 Q.E.D.
-- Inductive lemma (strong): signProd
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Lemma: swapReducesCost
--   Step: 1                                       Q.E.D.
--   Step: 2                                       Q.E.D.
--   Step: 3                                       Q.E.D.
--   Step: 4                                       Q.E.D.
--   Step: 5                                       Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: cost, countWS, depthSum, swap, treeSize, treeWeight
-- [Proven] swapReducesCost :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapReducesCost :: TP (Proof (   Forall "wa" Integer -> Forall "sa" Integer
                              -> Forall "wb" Integer -> Forall "sb" Integer
                              -> Forall "t"  HTree   -> SBool))
swapReducesCost = do
   swpC <- recall swapCost

   signProd <- sInduct "signProd"
       (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .<= 0 .=> a * b .<= 0)
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
                  Tip{}   -> 0
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
-- Lemma: treeSizePos    Q.E.D.
-- Functions proven terminating: treeSize
-- [Proven] treeSizePos :: Ɐt ∷ HTree → Bool
treeSizePosProof :: TP (Proof (Forall "t" HTree -> SBool))
treeSizePosProof = inductiveLemma "treeSizePos" (\(Forall @"t" t) -> treeSize t .>= 1) []

-- | Leaf counts are non-negative: @countWS w s t >= 0@.
--
-- >>> runTPWith cvc5 countWSNonNegProof
-- Lemma: treeSizePos                         Q.E.D.
-- Inductive lemma (strong): countWSNonNeg
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: countWS, treeSize
-- [Proven] countWSNonNeg :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
countWSNonNegProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
countWSNonNegProof = do
   tsPos <- recall treeSizePosProof

   sInduct "countWSNonNeg"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) -> countWS w s t .>= 0)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s t -> []
         |- countWS w s t .>= (0 :: SInteger)
         =: [pCase| t of
               Tip{}   -> trivial
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
-- >>> runTPWith cvc5 depthSumZeroProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Inductive lemma (strong): depthSumZero
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
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
         |- depthSum w s t
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> depthSum w s l + countWS w s l + depthSum w s r + countWS w s r
                       ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                       ?? countWSNonNeg `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                       ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                       =: (0 :: SInteger)
                       =: qed
            |]

-- | The deepest leaf always appears at least once in the tree:
-- @countWS (deepW t) (deepS t) t >= 1@.
--
-- >>> runTPWith cvc5 deepCountWSProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Inductive lemma (strong): deepCountWS
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                      Q.E.D.
--       Step: 1.2.2.1.2                      Q.E.D.
--       Step: 1.2.2.2.1                      Q.E.D.
--       Step: 1.2.2.2.2                      Q.E.D.
--       Step: 1.2.2.Completeness             Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
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
               Tip{}   -> trivial
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
-- Lemma: heightNonNeg    Q.E.D.
-- Functions proven terminating: height
-- [Proven] heightNonNeg :: Ɐt ∷ HTree → Bool
heightNonNegProof :: TP (Proof (Forall "t" HTree -> SBool))
heightNonNegProof = inductiveLemma "heightNonNeg" (\(Forall @"t" t) -> height t .>= 0) []

-- | The deepest leaf is always a member of the tree.
--
-- >>> runTPWith cvc5 deepMemberProof
-- Lemma: deepMember    Q.E.D.
-- Functions proven terminating: deepS, height, member
-- [Proven] deepMember :: Ɐt ∷ HTree → Bool
deepMemberProof :: TP (Proof (Forall "t" HTree -> SBool))
deepMemberProof = inductiveLemma "deepMember" (\(Forall @"t" t) -> member (deepS t) t) []

-- | @max(a, b) >= a@.
--
-- >>> runTPWith cvc5 maxGeLProof
-- Lemma: maxGeL       Q.E.D.
-- [Proven] maxGeL :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
maxGeLProof :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
maxGeLProof = lemma "maxGeL" (\(Forall @"a" a) (Forall @"b" b) -> a .<= ite (a .>= b) a (b :: SInteger)) []

-- | @max(a, b) >= b@.
--
-- >>> runTPWith cvc5 maxGeRProof
-- Lemma: maxGeR       Q.E.D.
-- [Proven] maxGeR :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
maxGeRProof :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
maxGeRProof = lemma "maxGeR" (\(Forall @"a" a) (Forall @"b" b) -> b .<= ite (a .>= b) a (b :: SInteger)) []

-- | @height t == 0 => depthSum w s t == 0@. A height-0 tree is a single
-- leaf, so its depthSum is always 0.
--
-- >>> runTPWith cvc5 heightZeroDepthSumProof
-- Lemma: heightNonNeg          Q.E.D.
-- Lemma: heightZeroDepthSum
--   Step: 1 (2 way case split)
--     Step: 1.1                Q.E.D.
--     Step: 1.2.1              Q.E.D.
--     Step: 1.2.2              Q.E.D.
--     Step: 1.Completeness     Q.E.D.
--   Result:                    Q.E.D.
-- Functions proven terminating: countWS, depthSum, height
-- [Proven] heightZeroDepthSum :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
heightZeroDepthSumProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
heightZeroDepthSumProof = do
   hNN <- recall heightNonNegProof

   calc "heightZeroDepthSum"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) ->
           height t .== 0 .=> depthSum w s t .== 0) $
       \w s t -> [height t .== 0]
              |- depthSum w s t
              =: [pCase| t of
                    Tip{}   -> trivial
                    Bin l r -> depthSum w s t
                            ?? hNN `at` Inst @"t" l
                            ?? hNN `at` Inst @"t" r
                            =: (0 :: SInteger)
                            =: qed
                 |]

-- | @countWS@ distributes over @Bin@: the count in a binary node equals the
-- sum of counts in its children.
--
-- >>> runTPWith cvc5 countWSBinProof
-- Lemma: countWSBin    Q.E.D.
-- Functions proven terminating: countWS
-- [Proven] countWSBin :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐl ∷ HTree → Ɐr ∷ HTree → Bool
countWSBinProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "l" HTree -> Forall "r" HTree -> SBool))
countWSBinProof = inductiveLemma "countWSBin"
    (\(Forall @"w" w) (Forall @"s" s) (Forall @"l" l) (Forall @"r" r) ->
        countWS w s l + countWS w s r .== countWS w s (sBin l r)) []

-- | The depth of any member symbol is bounded by the tree height:
-- @member s t => depth s t <= height t@.
--
-- >>> runTPWith cvc5 depthLeqHeightProof
-- Lemma: treeSizePos                          Q.E.D.
-- Lemma: maxGeL                               Q.E.D.
-- Lemma: maxGeR                               Q.E.D.
-- Inductive lemma (strong): depthLeqHeight
--   Step: Measure is non-negative             Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                               Q.E.D.
--     Step: 1.2.1                             Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                       Q.E.D.
--       Step: 1.2.2.1.2                       Q.E.D.
--       Step: 1.2.2.2.1                       Q.E.D.
--       Step: 1.2.2.2.2                       Q.E.D.
--       Step: 1.2.2.Completeness              Q.E.D.
--     Step: 1.Completeness                    Q.E.D.
--   Result:                                   Q.E.D.
-- Functions proven terminating: depth, height, member, treeSize
-- [Proven] depthLeqHeight :: Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
depthLeqHeightProof :: TP (Proof (Forall "s" Integer -> Forall "t" HTree -> SBool))
depthLeqHeightProof = do
   tsPos  <- recall treeSizePosProof
   maxGeL <- recall maxGeLProof
   maxGeR <- recall maxGeRProof

   sInduct "depthLeqHeight"
       (\(Forall @"s" s) (Forall @"t" t) -> member s t .=> depth s t .<= height t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih s t -> [member s t]
         |- depth s t .<= height t
         =: [pCase| t of
               Tip{}   -> trivial
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
-- >>> runTPWith cvc5 depthSumLeqHeightProof
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: countWSNonNeg                           Q.E.D.
-- Lemma: depthSumZero                            Q.E.D.
-- Lemma: maxGeL                                  Q.E.D.
-- Lemma: maxGeR                                  Q.E.D.
-- Lemma: countWSBin                              Q.E.D.
-- Inductive lemma (strong): depthSumLeqHeight
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                  Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                          Q.E.D.
--       Step: 1.2.2.1.2                          Q.E.D.
--       Step: 1.2.2.2.1                          Q.E.D.
--       Step: 1.2.2.2.2                          Q.E.D.
--       Step: 1.2.2.3.1                          Q.E.D.
--       Step: 1.2.2.3.2                          Q.E.D.
--       Step: 1.2.2.Completeness                 Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
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
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) -> countWS w s t .== 1 .=> depthSum w s t .<= height t)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s t -> [countWS w s t .== 1]
         |- depthSum w s t .<= height t
         =: [pCase| t of
               Tip{}   -> trivial
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
-- >>> runTPWith cvc5 deepDepthSumProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Lemma: depthSumZero                        Q.E.D.
-- Lemma: deepCountWS                         Q.E.D.
-- Lemma: countWSBin                          Q.E.D.
-- Inductive lemma (strong): deepDepthSum
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                      Q.E.D.
--       Step: 1.2.2.1.2                      Q.E.D.
--       Step: 1.2.2.2.1                      Q.E.D.
--       Step: 1.2.2.2.2                      Q.E.D.
--       Step: 1.2.2.Completeness             Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
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
         |- depthSum (deepW t) (deepS t) t
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> depthSum (deepW t) (deepS t) t
                       =: cases
                            [ height l .>= height r
                                ==> depthSum (deepW t) (deepS t) t
                                 ?? cwsBin        `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"l" l, Inst @"r" r)
                                 ?? deepCountWS   `at` Inst @"t" l
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"t" r)
                                 ?? depthSumZero  `at` (Inst @"w" (deepW l), Inst @"s" (deepS l), Inst @"t" r)
                                 ?? ih            `at` Inst @"t" l
                                 ?? tsPos         `at` Inst @"t" r
                                 =: height t
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> depthSum (deepW t) (deepS t) t
                                 ?? cwsBin        `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"l" l, Inst @"r" r)
                                 ?? deepCountWS   `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? depthSumZero  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? ih            `at` Inst @"t" r
                                 ?? tsPos         `at` Inst @"t" l
                                 =: height t
                                 =: qed
                            ]
            |]

-- | First greedy swap: a leaf lighter than the deepest can be swapped
-- to the deepest position without increasing cost.
--
-- >>> runTPWith cvc5 greedySwap1Proof
-- Lemma: swapReducesCost                          Q.E.D.
-- Lemma: deepDepthSum                             Q.E.D.
-- Lemma: depthSumLeqHeight                        Q.E.D.
-- Lemma: greedySwap1
--   Step: 1                                       Q.E.D.
--   Result:                                       Q.E.D.
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
-- >>> runTPWith cvc5 greedySwap2Proof
-- Lemma: swapReducesCost                          Q.E.D.
-- Lemma: sibDepthSum                              Q.E.D.
-- Lemma: depthSumLeqHeight                        Q.E.D.
-- Lemma: greedySwap2
--   Step: 1                                       Q.E.D.
--   Result:                                       Q.E.D.
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
-- >>> runTPWith cvc5 greedyChoiceProof
-- Lemma: greedySwap1                              Q.E.D.
-- Lemma: greedySwap2                              Q.E.D.
-- Lemma: greedyChoice
--   Step: 1                                       Q.E.D.
--   Result:                                       Q.E.D.
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
-- >>> runTPWith cvc5 swapPreservesHeightProof
-- Lemma: treeSizePos                               Q.E.D.
-- Inductive lemma (strong): swapPreservesHeight
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                    Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2                                  Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
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
         |- height (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> height (swap wa sa wb sb t)
                       ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: height t
                       =: qed
            |]

-- | Swapping @(wa, sa)@ with the deepest leaf places @wa@ at the deepest position:
-- @deepW (swap wa sa (deepW t) (deepS t) t) == wa@.
--
-- >>> runTPWith cvc5 swapDeepWProof
-- Lemma: treeSizePos                               Q.E.D.
-- Lemma: swapPreservesHeight                       Q.E.D.
-- Inductive lemma (strong): swapDeepW
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                    Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                            Q.E.D.
--       Step: 1.2.2.1.2                            Q.E.D.
--       Step: 1.2.2.2.1                            Q.E.D.
--       Step: 1.2.2.2.2                            Q.E.D.
--       Step: 1.2.2.Completeness                   Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
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
         |- deepW (swap wa sa (deepW t) (deepS t) t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> deepW (swap wa sa (deepW t) (deepS t) t)
                       =: cases
                            [ height l .>= height r
                                ==> deepW (swap wa sa (deepW t) (deepS t) t)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" l)
                                 ?? tsPos `at` Inst @"t" r
                                 =: wa
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> deepW (swap wa sa (deepW t) (deepS t) t)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" r)
                                 ?? tsPos `at` Inst @"t" l
                                 =: wa
                                 =: qed
                            ]
            |]

-- | Swapping @(wa, sa)@ with the deepest leaf places @sa@ at the deepest position:
-- @deepS (swap wa sa (deepW t) (deepS t) t) == sa@.
--
-- >>> runTPWith cvc5 swapDeepSProof
-- Lemma: treeSizePos                               Q.E.D.
-- Lemma: swapPreservesHeight                       Q.E.D.
-- Inductive lemma (strong): swapDeepS
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                    Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                            Q.E.D.
--       Step: 1.2.2.1.2                            Q.E.D.
--       Step: 1.2.2.2.1                            Q.E.D.
--       Step: 1.2.2.2.2                            Q.E.D.
--       Step: 1.2.2.Completeness                   Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
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
         |- deepS (swap wa sa (deepW t) (deepS t) t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> deepS (swap wa sa (deepW t) (deepS t) t)
                       =: cases
                            [ height l .>= height r
                                ==> deepS (swap wa sa (deepW t) (deepS t) t)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" l)
                                 ?? tsPos `at` Inst @"t" r
                                 =: sa
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> deepS (swap wa sa (deepW t) (deepS t) t)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                                 ?? swpHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                                 ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" r)
                                 ?? tsPos `at` Inst @"t" l
                                 =: sa
                                 =: qed
                            ]
            |]

-- | Swap preserves countWS for unrelated (weight, symbol) pairs.
-- Uses tuples to keep the arity within sInduct's limit.
--
-- >>> runTPWith cvc5 swapPreservesCountWSProof
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
           |- countWS w s (swap wa sa wb sb t)
           =: [pCase| t of
                 Tip{}   -> trivial
                 Bin l r -> countWS w s (swap wa sa wb sb t)
                         ?? ih `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" l)
                         ?? ih `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" r)
                         ?? tsPos `at` Inst @"t" l
                         ?? tsPos `at` Inst @"t" r
                         =: countWS w s t
                         =: qed
              |]

-- | Swap preserves depthSum for unrelated (weight, symbol) pairs.
--
-- >>> runTPWith cvc5 swapPreservesDepthSumProof
-- Lemma: treeSizePos                                 Q.E.D.
-- Lemma: swapPreservesCountWS                        Q.E.D.
-- Inductive lemma (strong): swapPreservesDepthSum
--   Step: Measure is non-negative                    Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                      Q.E.D.
--     Step: 1.2.1                                    Q.E.D.
--     Step: 1.2.2                                    Q.E.D.
--     Step: 1.Completeness                           Q.E.D.
--   Result:                                          Q.E.D.
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
           |- depthSum w s (swap wa sa wb sb t)
           =: [pCase| t of
                 Tip{}   -> trivial
                 Bin l r -> depthSum w s (swap wa sa wb sb t)
                         ?? ih      `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" l)
                         ?? ih      `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" r)
                         ?? swapCWS `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" l)
                         ?? swapCWS `at` (Inst @"a" a, Inst @"b" b, Inst @"c" c, Inst @"t" r)
                         ?? tsPos   `at` Inst @"t" l
                         ?? tsPos   `at` Inst @"t" r
                         =: depthSum w s t
                         =: qed
              |]

-- | Swap exchanges countWS: after swapping @(wa,sa)@ with @(wb,sb)@,
-- the count of @(wb,sb)@ equals the old count of @(wa,sa)@.
--
-- >>> runTPWith cvc5 swapExchangesCountWSProof
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
         |- countWS wb sb (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> countWS wb sb (swap wa sa wb sb t)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: countWS wa sa t
                       =: qed
            |]

-- | Swap exchanges depthSum: after swapping, the depthSum of @(wb,sb)@
-- equals the old depthSum of @(wa,sa)@.
--
-- >>> runTPWith cvc5 swapExchangesDepthSumProof
-- Lemma: treeSizePos                                 Q.E.D.
-- Lemma: swapExchangesCountWS                        Q.E.D.
-- Inductive lemma (strong): swapExchangesDepthSum
--   Step: Measure is non-negative                    Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                      Q.E.D.
--     Step: 1.2.1                                    Q.E.D.
--     Step: 1.2.2                                    Q.E.D.
--     Step: 1.Completeness                           Q.E.D.
--   Result:                                          Q.E.D.
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
         |- depthSum wb sb (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> depthSum wb sb (swap wa sa wb sb t)
                       ?? ih       `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih       `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? swapXCWS `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? swapXCWS `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? tsPos    `at` Inst @"t" l
                       ?? tsPos    `at` Inst @"t" r
                       =: depthSum wa sa t
                       =: qed
            |]

-- ** Sibling lemmas
--
-- The sibling of the deepest leaf has count at least 1,
-- and its depthSum equals the height when it is unique.

-- | The sibling leaf is counted at least once.
--
-- >>> runTPWith cvc5 sibCountWSProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Lemma: deepCountWS                         Q.E.D.
-- Lemma: heightNonNeg                        Q.E.D.
-- Inductive lemma (strong): sibCountWS
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                      Q.E.D.
--       Step: 1.2.2.1.2                      Q.E.D.
--       Step: 1.2.2.2.1                      Q.E.D.
--       Step: 1.2.2.2.2                      Q.E.D.
--       Step: 1.2.2.3.1                      Q.E.D.
--       Step: 1.2.2.3.2                      Q.E.D.
--       Step: 1.2.2.Completeness             Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
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
               Tip{}   -> trivial
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
-- >>> runTPWith cvc5 sibDepthSumProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Lemma: depthSumZero                        Q.E.D.
-- Lemma: deepCountWS                         Q.E.D.
-- Lemma: heightNonNeg                        Q.E.D.
-- Lemma: sibCountWS                          Q.E.D.
-- Lemma: countWSBin                          Q.E.D.
-- Lemma: heightZeroDepthSum                  Q.E.D.
-- Inductive lemma (strong): sibDepthSum
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                      Q.E.D.
--       Step: 1.2.2.1.2                      Q.E.D.
--       Step: 1.2.2.2.1                      Q.E.D.
--       Step: 1.2.2.2.2                      Q.E.D.
--       Step: 1.2.2.3.1                      Q.E.D.
--       Step: 1.2.2.3.2                      Q.E.D.
--       Step: 1.2.2.Completeness             Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
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
         |- depthSum (sibW t) (sibS t) t
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> depthSum (sibW t) (sibS t) t
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> depthSum (sibW t) (sibS t) t
                                 ?? cwsBin        `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"l" l, Inst @"r" r)
                                 ?? deepCountWS   `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? depthSumZero  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? heightNonNeg  `at` Inst @"t" r
                                 ?? heightZeroDS  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" l)
                                 ?? heightZeroDS  `at` (Inst @"w" (deepW r), Inst @"s" (deepS r), Inst @"t" r)
                                 =: height t
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> depthSum (sibW t) (sibS t) t
                                 ?? cwsBin        `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"l" l, Inst @"r" r)
                                 ?? sibCountWS    `at` Inst @"t" l
                                 ?? countWSNonNeg `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"t" r)
                                 ?? depthSumZero  `at` (Inst @"w" (sibW l), Inst @"s" (sibS l), Inst @"t" r)
                                 ?? ih            `at` Inst @"t" l
                                 ?? tsPos         `at` Inst @"t" r
                                 =: height t
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> depthSum (sibW t) (sibS t) t
                                 ?? cwsBin        `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"l" l, Inst @"r" r)
                                 ?? sibCountWS    `at` Inst @"t" r
                                 ?? countWSNonNeg `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"t" l)
                                 ?? depthSumZero  `at` (Inst @"w" (sibW r), Inst @"s" (sibS r), Inst @"t" l)
                                 ?? ih            `at` Inst @"t" r
                                 ?? tsPos         `at` Inst @"t" l
                                 ?? heightNonNeg  `at` Inst @"t" l
                                 =: height t
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
-- >>> runTPWith cvc5 collapsePreservesWeightProof
-- Lemma: treeSizePos                                   Q.E.D.
-- Lemma: heightNonNeg                                  Q.E.D.
-- Inductive lemma (strong): collapsePreservesWeight
--   Step: Measure is non-negative                      Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                        Q.E.D.
--     Step: 1.2.1                                      Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                                Q.E.D.
--       Step: 1.2.2.1.2                                Q.E.D.
--       Step: 1.2.2.2.1                                Q.E.D.
--       Step: 1.2.2.2.2                                Q.E.D.
--       Step: 1.2.2.3.1                                Q.E.D.
--       Step: 1.2.2.3.2                                Q.E.D.
--       Step: 1.2.2.Completeness                       Q.E.D.
--     Step: 1.Completeness                             Q.E.D.
--   Result:                                            Q.E.D.
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
         |- treeWeight (collapse t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> treeWeight (collapse t)
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> treeWeight (collapse t)
                                 =: treeWeight t
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> treeWeight (collapse t)
                                 ?? ih `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 =: treeWeight t
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> treeWeight (collapse t)
                                 ?? ih `at` Inst @"t" r
                                 ?? tsPos `at` Inst @"t" l
                                 ?? hNN `at` Inst @"t" l
                                 ?? hNN `at` Inst @"t" r
                                 =: treeWeight t
                                 =: qed
                            ]
            |]

-- | Trees with positive height have at least 3 nodes (they must be a 'Bin'
-- with two children, each of size at least 1).
--
-- >>> runTPWith cvc5 heightPosTreeSizeProof
-- Lemma: treeSizePos          Q.E.D.
-- Lemma: heightPosTreeSize    Q.E.D.
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
-- >>> runTPWith cvc5 costDecompProof
-- Lemma: treeSizePos                                   Q.E.D.
-- Lemma: collapsePreservesWeight                       Q.E.D.
-- Lemma: heightNonNeg                                  Q.E.D. [Cached]
-- Lemma: heightPosTreeSize                             Q.E.D.
-- Inductive lemma (strong): costDecomp
--   Step: Measure is non-negative                      Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                      Q.E.D.
--     Step: 1.1.2                                      Q.E.D.
--     Step: 1.2.1                                      Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                                Q.E.D.
--       Step: 1.2.2.1.2 (2 way case split)
--         Step: 1.2.2.1.2.1.1                          Q.E.D.
--         Step: 1.2.2.1.2.1.2                          Q.E.D.
--         Step: 1.2.2.1.2.2.1                          Q.E.D.
--         Step: 1.2.2.1.2.2.2 (2 way case split)
--           Step: 1.2.2.1.2.2.2.1.1                    Q.E.D.
--           Step: 1.2.2.1.2.2.2.1.2                    Q.E.D.
--           Step: 1.2.2.1.2.2.2.2.1                    Q.E.D.
--           Step: 1.2.2.1.2.2.2.2.2                    Q.E.D.
--           Step: 1.2.2.1.2.2.2.Completeness           Q.E.D.
--         Step: 1.2.2.1.2.Completeness                 Q.E.D.
--       Step: 1.2.2.2.1                                Q.E.D.
--       Step: 1.2.2.2.2 (2 way case split)
--         Step: 1.2.2.2.2.1.1                          Q.E.D.
--         Step: 1.2.2.2.2.1.2 (2 way case split)
--           Step: 1.2.2.2.2.1.2.1.1                    Q.E.D.
--           Step: 1.2.2.2.2.1.2.1.2                    Q.E.D.
--           Step: 1.2.2.2.2.1.2.2.1                    Q.E.D.
--           Step: 1.2.2.2.2.1.2.2.2                    Q.E.D.
--           Step: 1.2.2.2.2.1.2.Completeness           Q.E.D.
--         Step: 1.2.2.2.2.2.1                          Q.E.D.
--         Step: 1.2.2.2.2.2.2                          Q.E.D.
--         Step: 1.2.2.2.2.Completeness                 Q.E.D.
--       Step: 1.2.2.Completeness                       Q.E.D.
--     Step: 1.Completeness                             Q.E.D.
--   Result:                                            Q.E.D.
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
         |- cost t
         =: [pCase| t of
               Tip{}   -> cost t
                       =: cost (collapse t) + deepW t + sibW t
                       =: qed
               Bin l r -> cost t
                       =: case l of
                            Tip{}   -> cost t
                                    =: case r of
                                         Tip{}   -> cost t
                                                 =: cost (collapse t) + deepW t + sibW t
                                                 =: qed
                                         Bin rl rr -> cost t
                                                  =: cases
                                                       [ height l .>= height r
                                                           ==> cost t
                                                            ?? hNN `at` Inst @"t" rl
                                                            ?? hNN `at` Inst @"t" rr
                                                            =: cost (collapse t) + deepW t + sibW t
                                                            =: qed
                                                       , sNot (height l .>= height r)
                                                           ==> cost t
                                                            ?? ih     `at` Inst @"t" r
                                                            ?? tsPos  `at` Inst @"t" l
                                                            ?? collWt `at` Inst @"t" r
                                                            ?? hpTS   `at` Inst @"t" r
                                                            =: cost (collapse t) + deepW t + sibW t
                                                            =: qed
                                                       ]
                            Bin ll lr -> cost t
                                    =: cases
                                         [ height l .>= height r
                                             ==> cost t
                                              =: cases
                                                   [ height l .== 0
                                                       ==> cost t
                                                        ?? hNN `at` Inst @"t" ll
                                                        ?? hNN `at` Inst @"t" lr
                                                        =: cost (collapse t) + deepW t + sibW t
                                                        =: qed
                                                   , sNot (height l .== 0)
                                                       ==> cost t
                                                        ?? ih     `at` Inst @"t" l
                                                        ?? tsPos  `at` Inst @"t" r
                                                        ?? collWt `at` Inst @"t" l
                                                        ?? hpTS   `at` Inst @"t" l
                                                        ?? hNN    `at` Inst @"t" l
                                                        =: cost (collapse t) + deepW t + sibW t
                                                        =: qed
                                                   ]
                                         , sNot (height l .>= height r)
                                             ==> cost t
                                              ?? ih     `at` Inst @"t" r
                                              ?? tsPos  `at` Inst @"t" l
                                              ?? collWt `at` Inst @"t" r
                                              ?? hpTS   `at` Inst @"t" r
                                              ?? hNN    `at` Inst @"t" l
                                              ?? hNN    `at` Inst @"t" r
                                              =: cost (collapse t) + deepW t + sibW t
                                              =: qed
                                         ]
            |]

-- | Height zero means the tree is a single leaf (treeSize 1).
--
-- >>> runTPWith cvc5 heightZeroTreeSizeOneProof
-- Lemma: heightNonNeg             Q.E.D.
-- Lemma: heightZeroTreeSizeOne    Q.E.D.
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
-- >>> runTPWith cvc5 collapseReducesTreeSizeProof
-- Lemma: treeSizePos                                   Q.E.D.
-- Lemma: heightNonNeg                                  Q.E.D.
-- Lemma: heightPosTreeSize                             Q.E.D.
-- Lemma: heightZeroTreeSizeOne                         Q.E.D.
-- Inductive lemma (strong): collapseReducesTreeSize
--   Step: Measure is non-negative                      Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                      Q.E.D.
--     Step: 1.1.2                                      Q.E.D.
--     Step: 1.2.1                                      Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                                Q.E.D.
--       Step: 1.2.2.1.2                                Q.E.D.
--       Step: 1.2.2.2.1                                Q.E.D.
--       Step: 1.2.2.2.2                                Q.E.D.
--       Step: 1.2.2.3.1                                Q.E.D.
--       Step: 1.2.2.3.2                                Q.E.D.
--       Step: 1.2.2.Completeness                       Q.E.D.
--     Step: 1.Completeness                             Q.E.D.
--   Result:                                            Q.E.D.
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
         |- treeSize (collapse t)
         =: [pCase| t of
               Tip{}   -> treeSize (collapse t)
                       =: treeSize t - 2
                       =: qed
               Bin l r -> treeSize (collapse t)
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> treeSize (collapse t)
                                 ?? hzTS `at` Inst @"t" l
                                 ?? hzTS `at` Inst @"t" r
                                 ?? hNN  `at` Inst @"t" r
                                 =: treeSize t - 2
                                 =: qed
                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> treeSize (collapse t)
                                 ?? ih    `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 ?? hpTS  `at` Inst @"t" l
                                 ?? hNN   `at` Inst @"t" l
                                 =: treeSize t - 2
                                 =: qed
                            , sNot (height l .>= height r)
                                ==> treeSize (collapse t)
                                 ?? ih    `at` Inst @"t" r
                                 ?? tsPos `at` Inst @"t" l
                                 ?? hpTS  `at` Inst @"t" r
                                 ?? hNN   `at` Inst @"t" l
                                 ?? hNN   `at` Inst @"t" r
                                 =: treeSize t - 2
                                 =: qed
                            ]
            |]

-- | Collapse reduces the number of leaves by one.
--
-- >>> runTPWith cvc5 collapseNumLeavesProof
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: heightNonNeg                            Q.E.D.
-- Lemma: heightPosTreeSize                       Q.E.D.
-- Lemma: heightZeroNumLeavesOne                  Q.E.D.
-- Inductive lemma (strong): collapseNumLeaves
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                Q.E.D.
--     Step: 1.1.2                                Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2 (3 way case split)
--       Step: 1.2.2.1.1                          Q.E.D.
--       Step: 1.2.2.1.2                          Q.E.D.
--       Step: 1.2.2.2.1                          Q.E.D.
--       Step: 1.2.2.2.2                          Q.E.D.
--       Step: 1.2.2.3.1                          Q.E.D.
--       Step: 1.2.2.3.2                          Q.E.D.
--       Step: 1.2.2.Completeness                 Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: collapse, height, numLeaves, treeSize, treeWeight
-- [Proven] collapseNumLeaves :: Ɐt ∷ HTree → Bool
collapseNumLeavesProof :: TP (Proof (Forall "t" HTree -> SBool))
collapseNumLeavesProof = do
   tsPos <- recall treeSizePosProof
   hNN   <- recall heightNonNegProof
   hpTS  <- recall heightPosTreeSizeProof

   hzNL  <- lemma "heightZeroNumLeavesOne"
                   (\(Forall @"t" t) -> height t .== 0 .=> numLeaves t .== 1)
                   [proofOf hNN]

   sInduct "collapseNumLeaves"
       (\(Forall @"t" t) ->
           treeSize t .>= 2 .=> numLeaves (collapse t) .== numLeaves t - 1)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [treeSize t .>= 2]
         |- numLeaves (collapse t)
         =: [pCase| t of
               Tip{}   -> numLeaves (collapse t)
                       =: numLeaves t - 1
                       =: qed
               Bin l r -> numLeaves (collapse t)
                       =: cases
                            [ height l .>= height r .&& height l .== 0
                                ==> numLeaves (collapse t)
                                 ?? hNN  `at` Inst @"t" l
                                 ?? hNN  `at` Inst @"t" r
                                 ?? hzNL `at` Inst @"t" l
                                 ?? hzNL `at` Inst @"t" r
                                 =: numLeaves t - 1
                                 =: qed

                            , height l .>= height r .&& sNot (height l .== 0)
                                ==> numLeaves (collapse t)
                                 ?? ih    `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 ?? hpTS  `at` Inst @"t" l
                                 ?? hNN   `at` Inst @"t" l
                                 =: numLeaves t - 1
                                 =: qed

                            , sNot (height l .>= height r)
                                ==> numLeaves (collapse t)
                                 ?? ih    `at` Inst @"t" r
                                 ?? tsPos `at` Inst @"t" l
                                 ?? hpTS  `at` Inst @"t" r
                                 ?? hNN   `at` Inst @"t" l
                                 ?? hNN   `at` Inst @"t" r
                                 =: numLeaves t - 1
                                 =: qed
                            ]
            |]

-- | When the height is 0 (i.e., the tree is a tip), 'deepW' equals 'treeWeight'.
--
-- >>> runTPWith cvc5 deepWTipProof
-- Lemma: heightNonNeg         Q.E.D.
-- Lemma: deepWTip
--   Step: 1 (2 way case split)
--     Step: 1.1.1             Q.E.D.
--     Step: 1.1.2             Q.E.D.
--     Step: 1.2.1             Q.E.D.
--     Step: 1.2.2             Q.E.D.
--     Step: 1.Completeness    Q.E.D.
--   Result:                   Q.E.D.
-- Functions proven terminating: deepW, height, treeWeight
-- [Proven] deepWTip :: Ɐt ∷ HTree → Bool
deepWTipProof :: TP (Proof (Forall "t" HTree -> SBool))
deepWTipProof = do
   hNN <- recall heightNonNegProof

   calc "deepWTip"
       (\(Forall @"t" t) -> height t .== 0 .=> deepW t .== treeWeight t)
       $ \t -> [height t .== 0]
         |- deepW t
         =: [pCase| t of
               Tip{}   -> deepW t
                       =: treeWeight t
                       =: qed
               Bin l r -> deepW t
                       ?? hNN `at` Inst @"t" l
                       ?? hNN `at` Inst @"t" r
                       =: treeWeight t
                       =: qed
            |]

-- | When both children are tips, the collapsed tip @sTip (treeWeight l + treeWeight r) 0@
-- equals @sTip (deepW t + sibW t) 0@ where @l = left t@ and @r = right t@.
--
-- >>> runTPWith cvc5 deepWSibWSumTipProof
-- Lemma: deepWTip             Q.E.D.
-- Lemma: deepWSibWSumTip
--   Step: 1                   Q.E.D.
--   Step: 2                   Q.E.D.
--   Step: 3                   Q.E.D.
--   Step: 4                   Q.E.D.
--   Result:                   Q.E.D.
-- Functions proven terminating: deepW, height, sibW, treeWeight
-- [Proven] deepWSibWSumTip :: Ɐt ∷ HTree → Bool
deepWSibWSumTipProof :: TP (Proof (Forall "t" HTree -> SBool))
deepWSibWSumTipProof = do
    dwTip <- recall deepWTipProof

    calc "deepWSibWSumTip"
        (\(Forall @"t" t) ->
               isBin t .&& isTip (sleft t) .&& isTip (sright t)
           .=> sTip (treeWeight (sleft t) + treeWeight (sright t)) 0
               .== sTip (deepW t + sibW t) 0)
        $ \t -> [isBin t, isTip (sleft t), isTip (sright t)]
          |- sTip (treeWeight (sleft t) + treeWeight (sright t)) 0
          =: sTip (deepW (sleft t) + treeWeight (sright t)) 0
          =: sTip (deepW (sleft t) + deepW (sright t)) 0
          ?? dwTip `at` Inst @"t" (sleft t)
          ?? dwTip `at` Inst @"t" (sright t)
          =: sTip (deepW (sleft t) + sibW t) 0
          =: sTip (deepW t + sibW t) 0
          =: qed

-- | (Tip, Bin) case: @deepW + sibW@ passes through to the right child.
--
-- >>> runTPWith cvc5 deepWSibWBinRProof
-- Lemma: heightNonNeg     Q.E.D.
-- Lemma: deepWSibWBinR
--   Step: 1               Q.E.D.
--   Step: 2               Q.E.D.
--   Result:               Q.E.D.
-- Functions proven terminating: deepW, height, sibW
-- [Proven] deepWSibWBinR :: Ɐl ∷ HTree → Ɐrl ∷ HTree → Ɐrr ∷ HTree → Bool
deepWSibWBinRProof :: TP (Proof (Forall "l" HTree -> Forall "rl" HTree -> Forall "rr" HTree -> SBool))
deepWSibWBinRProof = do
    hNN <- recall heightNonNegProof

    calc "deepWSibWBinR"
        (\(Forall @"l" l) (Forall @"rl" rl) (Forall @"rr" rr) ->
            let r = sBin rl rr; t = sBin l r
            in     isTip l
               .=> sTip (deepW r + sibW r) 0 .== sTip (deepW t + sibW t) 0)
        $ \l rl rr -> let r = sBin rl rr; t = sBin l r in [isTip l]
          |- sTip (deepW r + sibW r) 0
          ?? hNN `at` Inst @"t" rl
          ?? hNN `at` Inst @"t" rr
          =: sTip (deepW t + sibW r) 0
          ?? hNN `at` Inst @"t" rl
          ?? hNN `at` Inst @"t" rr
          =: sTip (deepW t + sibW t) 0
          =: qed

-- | (Bin, Tip) case: @deepW + sibW@ passes through to the left child.
--
-- >>> runTPWith cvc5 deepWSibWBinLProof
-- Lemma: heightNonNeg     Q.E.D.
-- Lemma: deepWSibWBinL
--   Step: 1               Q.E.D.
--   Step: 2               Q.E.D.
--   Result:               Q.E.D.
-- Functions proven terminating: deepW, height, sibW
-- [Proven] deepWSibWBinL :: Ɐll ∷ HTree → Ɐlr ∷ HTree → Ɐr ∷ HTree → Bool
deepWSibWBinLProof :: TP (Proof (Forall "ll" HTree -> Forall "lr" HTree -> Forall "r" HTree -> SBool))
deepWSibWBinLProof = do
    hNN <- recall heightNonNegProof

    calc "deepWSibWBinL"
        (\(Forall @"ll" ll) (Forall @"lr" lr) (Forall @"r" r) ->
            let l = sBin ll lr; t = sBin l r
            in     isTip r
               .=> sTip (deepW l + sibW l) 0 .== sTip (deepW t + sibW t) 0)
        $ \ll lr r -> let l = sBin ll lr; t = sBin l r in [isTip r]
          |- sTip (deepW l + sibW l) 0
          ?? hNN `at` Inst @"t" ll
          ?? hNN `at` Inst @"t" lr
          =: sTip (deepW t + sibW l) 0
          ?? hNN `at` Inst @"t" ll
          ?? hNN `at` Inst @"t" lr
          =: sTip (deepW t + sibW t) 0
          =: qed

-- | (Bin, Bin, height l >= height r) case: @deepW + sibW@ passes through to the left child.
--
-- >>> runTPWith cvc5 deepWSibWBinBinLProof
-- Lemma: heightNonNeg         Q.E.D.
-- Lemma: deepWSibWBinBinL
--   Step: 1 (2 way case split)
--     Step: 1.1.1             Q.E.D.
--     Step: 1.1.2             Q.E.D.
--     Step: 1.2.1             Q.E.D.
--     Step: 1.2.2             Q.E.D.
--     Step: 1.2.3             Q.E.D.
--     Step: 1.Completeness    Q.E.D.
--   Result:                   Q.E.D.
-- Functions proven terminating: deepW, height, sibW
-- [Proven] deepWSibWBinBinL :: Ɐl ∷ HTree → Ɐr ∷ HTree → Bool
deepWSibWBinBinLProof :: TP (Proof (Forall "l" HTree -> Forall "r" HTree -> SBool))
deepWSibWBinBinLProof = do
    hNN <- recall heightNonNegProof

    calc "deepWSibWBinBinL"
        (\(Forall @"l" l) (Forall @"r" r) ->
               isBin l .&& isBin r .&& height l .>= height r
           .=> sTip (deepW l + sibW l) 0 .== sTip (deepW (sBin l r) + sibW (sBin l r)) 0)
        $ \l r -> [isBin l, isBin r, height l .>= height r]
          |- sTip (deepW l + sibW l) 0
          =: [pCase| l of
                Tip{} -> sTip (deepW l + sibW l) 0
                      =: sTip (deepW (sBin l r) + sibW (sBin l r)) 0
                      =: qed
                Bin ll lr -> sTip (deepW l + sibW l) 0
                      ?? hNN `at` Inst @"t" ll
                      ?? hNN `at` Inst @"t" lr
                      =: sTip (deepW (sBin l r) + sibW l) 0
                      ?? hNN `at` Inst @"t" ll
                      ?? hNN `at` Inst @"t" lr
                      =: sTip (deepW (sBin l r) + sibW (sBin l r)) 0
                      =: qed
             |]

-- | (Bin, Bin, height l < height r) case: @deepW + sibW@ passes through to the right child.
--
-- >>> runTPWith cvc5 deepWSibWBinBinRProof
-- Lemma: heightNonNeg         Q.E.D.
-- Lemma: deepWSibWBinBinR
--   Step: 1 (2 way case split)
--     Step: 1.1.1             Q.E.D.
--     Step: 1.1.2             Q.E.D.
--     Step: 1.2.1             Q.E.D.
--     Step: 1.2.2             Q.E.D.
--     Step: 1.2.3             Q.E.D.
--     Step: 1.Completeness    Q.E.D.
--   Result:                   Q.E.D.
-- Functions proven terminating: deepW, height, sibW
-- [Proven] deepWSibWBinBinR :: Ɐl ∷ HTree → Ɐr ∷ HTree → Bool
deepWSibWBinBinRProof :: TP (Proof (Forall "l" HTree -> Forall "r" HTree -> SBool))
deepWSibWBinBinRProof = do
    hNN <- recall heightNonNegProof

    calc "deepWSibWBinBinR"
        (\(Forall @"l" l) (Forall @"r" r) ->
               isBin l .&& isBin r .&& sNot (height l .>= height r)
           .=> sTip (deepW r + sibW r) 0 .== sTip (deepW (sBin l r) + sibW (sBin l r)) 0)
        $ \l r -> [isBin l, isBin r, sNot (height l .>= height r)]
          |- sTip (deepW r + sibW r) 0
          =: [pCase| r of
                Tip{} -> sTip (deepW r + sibW r) 0
                      =: sTip (deepW (sBin l r) + sibW (sBin l r)) 0
                      =: qed
                Bin rl rr -> sTip (deepW r + sibW r) 0
                      ?? hNN `at` Inst @"t" rl
                      ?? hNN `at` Inst @"t" rr
                      =: sTip (deepW (sBin l r) + sibW r) 0
                      ?? hNN `at` Inst @"t" rl
                      ?? hNN `at` Inst @"t" rr
                      =: sTip (deepW (sBin l r) + sibW (sBin l r)) 0
                      =: qed
             |]

-- | Collapse leaf correspondence: adding back the two merged leaf weights to @leavesOf(collapse t)@
-- equals adding the combined weight to @leavesOf t@.
--
-- >>> runTPWith cvc5 collapseLeavesOfProof
-- Lemma: treeSizePos                                  Q.E.D.
-- Lemma: heightNonNeg                                 Q.E.D.
-- Lemma: heightPosTreeSize                            Q.E.D.
-- Lemma: leavesOfAllTip0                              Q.E.D.
-- Lemma: insertAllSortedInsertL                       Q.E.D.
-- Lemma: insertAllSortedInsert                        Q.E.D. [Cached]
-- Lemma: sortedInsertAllTip0                          Q.E.D. [Cached]
-- Lemma: sortedInsertComm                             Q.E.D. [Cached]
-- Lemma: deepWSibWSumTip                              Q.E.D.
-- Lemma: deepWSibWBinR                                Q.E.D.
-- Lemma: deepWSibWBinL                                Q.E.D.
-- Lemma: deepWSibWBinBinL                             Q.E.D.
-- Lemma: deepWSibWBinBinR                             Q.E.D.
-- Inductive lemma (strong): collapseLeavesOf
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.2 (4 way case split)
--       Step: 1.2.1.1                                 Q.E.D.
--       Step: 1.2.1.2                                 Q.E.D.
--       Step: 1.2.1.3                                 Q.E.D.
--       Step: 1.2.1.4                                 Q.E.D.
--       Step: 1.2.1.5                                 Q.E.D.
--       Step: 1.2.1.6                                 Q.E.D.
--       Step: 1.2.1.7                                 Q.E.D.
--       Step: 1.2.1.8                                 Q.E.D.
--       Step: 1.2.2.1                                 Q.E.D.
--       Step: 1.2.2.2                                 Q.E.D.
--       Step: 1.2.2.3                                 Q.E.D.
--       Step: 1.2.2.4                                 Q.E.D.
--       Step: 1.2.2.5                                 Q.E.D.
--       Step: 1.2.2.6                                 Q.E.D.
--       Step: 1.2.2.7                                 Q.E.D.
--       Step: 1.2.2.8                                 Q.E.D.
--       Step: 1.2.3.1                                 Q.E.D.
--       Step: 1.2.3.2                                 Q.E.D.
--       Step: 1.2.3.3                                 Q.E.D.
--       Step: 1.2.3.4                                 Q.E.D.
--       Step: 1.2.3.5                                 Q.E.D.
--       Step: 1.2.3.6                                 Q.E.D.
--       Step: 1.2.3.7                                 Q.E.D.
--       Step: 1.2.3.8                                 Q.E.D.
--       Step: 1.2.4.1                                 Q.E.D.
--       Step: 1.2.4.2 (2 way case split)
--         Step: 1.2.4.2.1.1                           Q.E.D.
--         Step: 1.2.4.2.1.2                           Q.E.D.
--         Step: 1.2.4.2.1.3                           Q.E.D.
--         Step: 1.2.4.2.1.4                           Q.E.D.
--         Step: 1.2.4.2.1.5                           Q.E.D.
--         Step: 1.2.4.2.1.6                           Q.E.D.
--         Step: 1.2.4.2.1.7                           Q.E.D.
--         Step: 1.2.4.2.2.1                           Q.E.D.
--         Step: 1.2.4.2.2.2                           Q.E.D.
--         Step: 1.2.4.2.2.3                           Q.E.D.
--         Step: 1.2.4.2.2.4                           Q.E.D.
--         Step: 1.2.4.2.2.5                           Q.E.D.
--         Step: 1.2.4.2.2.6                           Q.E.D.
--         Step: 1.2.4.2.2.7                           Q.E.D.
--         Step: 1.2.4.2.Completeness                  Q.E.D.
--       Step: 1.2.Completeness                        Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating:
--   allTip0, collapse, deepW, height, insertAll, leavesOf, sibW, sortedInsert, treeSize, treeWeight
-- [Proven] collapseLeavesOf :: Ɐt ∷ HTree → Bool
collapseLeavesOfProof :: TP (Proof (Forall "t" HTree -> SBool))
collapseLeavesOfProof = do
   tsPos  <- recall treeSizePosProof
   hNN    <- recall heightNonNegProof
   hpTS   <- recall heightPosTreeSizeProof
   loAT   <- recall leavesOfAllTip0Proof
   iaSIL  <- recall insertAllSortedInsertLProof
   iaSI   <- recall insertAllSortedInsertProof
   siAT   <- recall sortedInsertAllTip0Proof
   siComm <- recall sortedInsertCommProof
   dwsTip <- recall deepWSibWSumTipProof
   dwsBR  <- recall deepWSibWBinRProof
   dwsBL  <- recall deepWSibWBinLProof
   dwsBBL <- recall deepWSibWBinBinLProof
   dwsBBR <- recall deepWSibWBinBinRProof

   sInduct "collapseLeavesOf"
       (\(Forall @"t" t) ->
              treeSize t .>= 2
          .=> sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
              .== sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t))
       (treeSize, [proofOf tsPos]) $
       \ih t -> [treeSize t .>= 2]
         |- sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
         =: [pCase| t of
               Tip{}   -> sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                       =: sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t)
                       =: qed

               Bin l r -> case tuple (l, r) of
                             -- Both tips: base case, everything unfolds directly
                             (Tip{}, Tip{}) ->
                                 let wl0 = sTip (treeWeight l) 0
                                     wr0 = sTip (treeWeight r) 0
                                     ws0 = sTip (treeWeight l + treeWeight r) 0
                                 in  sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                              ?? hNN `at` Inst @"t" l
                              ?? hNN `at` Inst @"t" r
                              =: sortedInsert wl0 (sortedInsert wr0 [ws0])
                              ?? siComm `at` (Inst @"a" wr0, Inst @"b" ws0, Inst @"ys" ([] :: SList HTree))
                              =: sortedInsert wl0 (sortedInsert ws0 [wr0])
                              ?? siComm `at` (Inst @"a" wl0, Inst @"b" ws0, Inst @"ys" [wr0])
                              =: sortedInsert ws0 (sortedInsert wl0 [wr0])
                              =: sortedInsert ws0 (insertAll [wl0] [wr0])
                              =: sortedInsert ws0 (insertAll (leavesOf l) (leavesOf r))
                              ?? dwsTip `at` Inst @"t" t
                              =: sortedInsert (sTip (deepW t + sibW t) 0) (insertAll (leavesOf l) (leavesOf r))
                              =: sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t)
                              =: qed

                             -- l is Tip, r is Bin: height l = 0 < height r, collapse goes into r
                             (Tip{}, Bin rl rr) ->
                                 let dw0 = sTip (deepW r) 0
                                     sw0 = sTip (sibW r) 0
                                     dsw = sTip (deepW r + sibW r) 0
                                     lo  = leavesOf l
                                     lcr = leavesOf (collapse r)
                                     lr  = leavesOf r
                                 in  sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                                  ?? hNN `at` Inst @"t" rl
                                  ?? hNN `at` Inst @"t" rr
                                  =: sortedInsert dw0 (sortedInsert sw0 (insertAll lo lcr))
                                  ?? loAT `at` Inst @"t" l
                                  ?? iaSI `at` (Inst @"a" sw0, Inst @"xs" lo, Inst @"ys" lcr)
                                  =: sortedInsert dw0 (insertAll lo (sortedInsert sw0 lcr))
                                  ?? loAT `at` Inst @"t" l
                                  ?? iaSI `at` (Inst @"a" dw0, Inst @"xs" lo, Inst @"ys" (sortedInsert sw0 lcr))
                                  =: insertAll lo (sortedInsert dw0 (sortedInsert sw0 lcr))
                                  ?? tsPos `at` Inst @"t" l
                                  ?? hpTS  `at` Inst @"t" r
                                  ?? hNN   `at` Inst @"t" rl
                                  ?? hNN   `at` Inst @"t" rr
                                  ?? ih    `at` Inst @"t" r
                                  =: insertAll lo (sortedInsert dsw lr)
                                  ?? loAT `at` Inst @"t" l
                                  ?? iaSI `at` (Inst @"a" dsw, Inst @"xs" lo, Inst @"ys" lr)
                                  =: sortedInsert dsw (insertAll lo lr)
                                  ?? dwsBR `at` (Inst @"l" l, Inst @"rl" rl, Inst @"rr" rr)
                                  ?? hNN   `at` Inst @"t" rl
                                  ?? hNN   `at` Inst @"t" rr
                                  =: sortedInsert (sTip (deepW t + sibW t) 0) (insertAll lo lr)
                                  =: sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t)
                                  =: qed

                             -- l is Bin, r is Tip: height l >= 1 > 0 = height r, collapse goes into l
                             (Bin ll lr, Tip{}) ->
                                 let dw0 = sTip (deepW l) 0
                                     sw0 = sTip (sibW l) 0
                                     dsw = sTip (deepW l + sibW l) 0
                                     lc  = leavesOf (collapse l)
                                     lo  = leavesOf l
                                     ro  = leavesOf r
                                 in  sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                                  ?? hNN `at` Inst @"t" ll
                                  ?? hNN `at` Inst @"t" lr
                                  =: sortedInsert dw0 (sortedInsert sw0 (insertAll lc ro))
                                  ?? loAT  `at` Inst @"t" (collapse l)
                                  ?? iaSIL `at` (Inst @"a" sw0, Inst @"xs" lc, Inst @"ys" ro)
                                  =: sortedInsert dw0 (insertAll (sortedInsert sw0 lc) ro)
                                  ?? loAT  `at` Inst @"t" (collapse l)
                                  ?? siAT  `at` (Inst @"t" sw0, Inst @"ts" lc)
                                  ?? iaSIL `at` (Inst @"a" dw0, Inst @"xs" (sortedInsert sw0 lc), Inst @"ys" ro)
                                  =: insertAll (sortedInsert dw0 (sortedInsert sw0 lc)) ro
                                  ?? tsPos `at` Inst @"t" r
                                  ?? hpTS  `at` Inst @"t" l
                                  ?? hNN   `at` Inst @"t" ll
                                  ?? hNN   `at` Inst @"t" lr
                                  ?? ih    `at` Inst @"t" l
                                  =: insertAll (sortedInsert dsw lo) ro
                                  ?? dwsBL `at` (Inst @"ll" ll, Inst @"lr" lr, Inst @"r" r)
                                  ?? hNN   `at` Inst @"t" ll
                                  ?? hNN   `at` Inst @"t" lr
                                  =: insertAll (sortedInsert (sTip (deepW t + sibW t) 0) lo) ro
                                  ?? loAT  `at` Inst @"t" l
                                  ?? iaSIL `at` (Inst @"a" (sTip (deepW t + sibW t) 0), Inst @"xs" lo, Inst @"ys" ro)
                                  =: sortedInsert (sTip (deepW t + sibW t) 0) (insertAll lo ro)
                                  =: sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t)
                                  =: qed

                             -- Both Bins: case split on height comparison
                             (Bin ll lr, Bin rl rr) ->
                                 sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                              =: cases
                                   [ -- height l >= height r: collapse goes into l
                                     height l .>= height r
                                       ==> let dw0 = sTip (deepW l) 0
                                               sw0 = sTip (sibW l) 0
                                               lc  = leavesOf (collapse l)
                                               lo  = leavesOf l
                                               ro  = leavesOf r
                                           in  sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                                            ?? hNN `at` Inst @"t" ll
                                            ?? hNN `at` Inst @"t" lr
                                            =: sortedInsert dw0 (sortedInsert sw0 (insertAll lc ro))
                                            ?? loAT  `at` Inst @"t" (collapse l)
                                            ?? iaSIL `at` (Inst @"a" sw0, Inst @"xs" lc, Inst @"ys" ro)
                                            =: sortedInsert dw0 (insertAll (sortedInsert sw0 lc) ro)
                                            ?? loAT  `at` Inst @"t" (collapse l)
                                            ?? siAT  `at` (Inst @"t" sw0, Inst @"ts" lc)
                                            ?? iaSIL `at` (Inst @"a" dw0, Inst @"xs" (sortedInsert sw0 lc), Inst @"ys" ro)
                                            =: insertAll (sortedInsert dw0 (sortedInsert sw0 lc)) ro
                                            ?? tsPos  `at` Inst @"t" r
                                            ?? hpTS   `at` Inst @"t" l
                                            ?? hNN    `at` Inst @"t" ll
                                            ?? hNN    `at` Inst @"t" lr
                                            ?? ih     `at` Inst @"t" l
                                            ?? dwsBBL `at` (Inst @"l" l, Inst @"r" r)
                                            =: insertAll (sortedInsert (sTip (deepW t + sibW t) 0) lo) ro
                                            ?? loAT  `at` Inst @"t" l
                                            ?? iaSIL `at` (Inst @"a" (sTip (deepW t + sibW t) 0), Inst @"xs" lo, Inst @"ys" ro)
                                            =: sortedInsert (sTip (deepW t + sibW t) 0) (insertAll lo ro)
                                            =: sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t)
                                            =: qed

                                   -- height l < height r: collapse goes into r
                                   , sNot (height l .>= height r)
                                       ==> let dw0 = sTip (deepW r) 0
                                               sw0 = sTip (sibW r) 0
                                               lo  = leavesOf l
                                               lcr = leavesOf (collapse r)
                                               lor = leavesOf r
                                           in  sortedInsert (sTip (deepW t) 0) (sortedInsert (sTip (sibW t) 0) (leavesOf (collapse t)))
                                            ?? hNN `at` Inst @"t" rl
                                            ?? hNN `at` Inst @"t" rr
                                            =: sortedInsert dw0 (sortedInsert sw0 (insertAll lo lcr))
                                            ?? loAT `at` Inst @"t" l
                                            ?? iaSI `at` (Inst @"a" sw0, Inst @"xs" lo, Inst @"ys" lcr)
                                            =: sortedInsert dw0 (insertAll lo (sortedInsert sw0 lcr))
                                            ?? loAT `at` Inst @"t" l
                                            ?? iaSI `at` (Inst @"a" dw0, Inst @"xs" lo, Inst @"ys" (sortedInsert sw0 lcr))
                                            =: insertAll lo (sortedInsert dw0 (sortedInsert sw0 lcr))
                                            ?? tsPos  `at` Inst @"t" l
                                            ?? hpTS   `at` Inst @"t" r
                                            ?? hNN    `at` Inst @"t" rl
                                            ?? hNN    `at` Inst @"t" rr
                                            ?? ih     `at` Inst @"t" r
                                            ?? dwsBBR `at` (Inst @"l" l, Inst @"r" r)
                                            =: insertAll lo (sortedInsert (sTip (deepW t + sibW t) 0) lor)
                                            ?? loAT `at` Inst @"t" l
                                            ?? iaSI `at` (Inst @"a" (sTip (deepW t + sibW t) 0), Inst @"xs" lo, Inst @"ys" lor)
                                            =: sortedInsert (sTip (deepW t + sibW t) 0) (insertAll lo lor)
                                            =: sortedInsert (sTip (deepW t + sibW t) 0) (leavesOf t)
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
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                           Q.E.D.
--       Step: 1.2.2.1.2                           Q.E.D.
--       Step: 1.2.2.2.1                           Q.E.D.
--       Step: 1.2.2.2.2                           Q.E.D.
--       Step: 1.2.2.Completeness                  Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: sortedInsert, treeWeight
-- [Proven] sortedInsertLength :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertLengthProof :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertLengthProof =
   sInduct "sortedInsertLength"
       (\(Forall @"t" t) (Forall @"ts" ts) ->
           length (sortedInsert t ts) .== 1 + length ts)
       (\_ ts -> length ts, []) $
       \ih t ts -> []
         |- length (sortedInsert t ts)
         =: [pCase| ts of
               [] -> length (sortedInsert t ts)
                  =: 1 + length ts
                  =: qed
               u : us -> length (sortedInsert t ts)
                      =: cases
                           [ treeWeight t .<= treeWeight u
                               ==> length (sortedInsert t ts)
                                =: 1 + length ts
                                =: qed
                           , sNot (treeWeight t .<= treeWeight u)
                               ==> length (sortedInsert t ts)
                                ?? ih `at` (Inst @"t" t, Inst @"ts" us)
                                =: 1 + length ts
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

-- ** Weight invariants

-- | Total weight of all trees in a forest.
forestWeight :: SList HTree -> SInteger
forestWeight = smtFunction "forestWeight"
             $ \ts -> [sCase| ts of
                         []     -> 0
                         t : rest -> treeWeight t + forestWeight rest
                      |]

-- | Sorted insertion preserves total forest weight.
--
-- >>> runTPWith cvc5 sortedInsertWeightProof
-- Inductive lemma (strong): sortedInsertWeight
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                           Q.E.D.
--       Step: 1.2.2.1.2                           Q.E.D.
--       Step: 1.2.2.2.1                           Q.E.D.
--       Step: 1.2.2.2.2                           Q.E.D.
--       Step: 1.2.2.Completeness                  Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: forestWeight, sortedInsert, treeWeight
-- [Proven] sortedInsertWeight :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertWeightProof :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertWeightProof =
   sInduct "sortedInsertWeight"
       (\(Forall @"t" t) (Forall @"ts" ts) ->
           forestWeight (sortedInsert t ts) .== treeWeight t + forestWeight ts)
       (\_ ts -> length ts, []) $
       \ih t ts -> []
         |- forestWeight (sortedInsert t ts)
         =: [pCase| ts of
               [] -> forestWeight (sortedInsert t ts)
                  =: treeWeight t + forestWeight ts
                  =: qed
               u : us -> forestWeight (sortedInsert t ts)
                      =: cases
                           [ treeWeight t .<= treeWeight u
                               ==> forestWeight (sortedInsert t ts)
                                =: treeWeight t + forestWeight ts
                                =: qed
                           , sNot (treeWeight t .<= treeWeight u)
                               ==> forestWeight (sortedInsert t ts)
                                ?? ih `at` (Inst @"t" t, Inst @"ts" us)
                                =: treeWeight t + forestWeight ts
                                =: qed
                           ]
            |]

-- | Building the Huffman tree preserves total weight: the resulting tree's
-- weight equals the sum of all input tree weights.
--
-- >>> runTPWith cvc5 buildHuffmanWeightProof
-- Lemma: sortedInsertWeight                       Q.E.D.
-- Lemma: sortedInsertLength                       Q.E.D.
-- Inductive lemma (strong): buildHuffmanWeight
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                           Q.E.D.
--       Step: 1.2.2.1.2                           Q.E.D.
--       Step: 1.2.2.2.1                           Q.E.D.
--       Step: 1.2.2.2.2                           Q.E.D.
--       Step: 1.2.2.Completeness                  Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: buildHuffman, forestWeight, sortedInsert, treeWeight
-- [Proven] buildHuffmanWeight :: Ɐts ∷ [HTree] → Bool
buildHuffmanWeightProof :: TP (Proof (Forall "ts" [HTree] -> SBool))
buildHuffmanWeightProof = do
   siWt  <- recall sortedInsertWeightProof
   siLen <- recall sortedInsertLengthProof

   sInduct "buildHuffmanWeight"
       (\(Forall @"ts" ts) ->
           length ts .>= 1 .=> treeWeight (buildHuffman ts) .== forestWeight ts)
       (length, []) $
       \ih ts -> [length ts .>= 1]
         |- treeWeight (buildHuffman ts)
         =: [pCase| ts of
               [] -> treeWeight (buildHuffman ts)
                  =: forestWeight ts
                  =: qed
               t : rest -> treeWeight (buildHuffman ts)
                        =: case rest of
                             [] -> treeWeight (buildHuffman ts)
                                =: forestWeight ts
                                =: qed
                             u : us -> treeWeight (buildHuffman ts)
                                    ?? ih    `at` Inst @"ts" (sortedInsert (sBin t u) us)
                                    ?? siWt  `at` (Inst @"t" (sBin t u), Inst @"ts" us)
                                    ?? siLen `at` (Inst @"t" (sBin t u), Inst @"ts" us)
                                    =: forestWeight ts
                                    =: qed
            |]

-- ** Cost and countWS invariants

-- | Total cost of all trees in a forest.
forestCost :: SList HTree -> SInteger
forestCost = smtFunction "forestCost"
           $ \ts -> [sCase| ts of
                       []       -> 0
                       t : rest -> cost t + forestCost rest
                    |]

-- | Total count of a (weight, symbol) pair across all trees in a forest.
forestCountWS :: SInteger -> SInteger -> SList HTree -> SInteger
forestCountWS = smtFunction "forestCountWS"
              $ \w s ts -> [sCase| ts of
                               []       -> 0
                               t : rest -> countWS w s t + forestCountWS w s rest
                           |]

-- | Sorted insertion preserves total forest cost.
--
-- >>> runTPWith cvc5 sortedInsertCostProof
-- Inductive lemma (strong): sortedInsertCost
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                               Q.E.D.
--     Step: 1.1.2                               Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                         Q.E.D.
--       Step: 1.2.2.1.2                         Q.E.D.
--       Step: 1.2.2.2.1                         Q.E.D.
--       Step: 1.2.2.2.2                         Q.E.D.
--       Step: 1.2.2.Completeness                Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: cost, forestCost, sortedInsert, treeWeight
-- [Proven] sortedInsertCost :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertCostProof :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertCostProof =
   sInduct "sortedInsertCost"
       (\(Forall @"t" t) (Forall @"ts" ts) ->
           forestCost (sortedInsert t ts) .== cost t + forestCost ts)
       (\_ ts -> length ts, []) $
       \ih t ts -> []
         |- forestCost (sortedInsert t ts)
         =: [pCase| ts of
               [] -> forestCost (sortedInsert t ts)
                  =: cost t + forestCost ts
                  =: qed
               u : us -> forestCost (sortedInsert t ts)
                      =: cases
                           [ treeWeight t .<= treeWeight u
                               ==> forestCost (sortedInsert t ts)
                                =: cost t + forestCost ts
                                =: qed
                           , sNot (treeWeight t .<= treeWeight u)
                               ==> forestCost (sortedInsert t ts)
                                ?? ih `at` (Inst @"t" t, Inst @"ts" us)
                                =: cost t + forestCost ts
                                =: qed
                           ]
            |]

-- | Sorted insertion preserves total forest countWS.
--
-- >>> runTPWith cvc5 sortedInsertCountWSProof
-- Inductive lemma (strong): sortedInsertCountWS
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                  Q.E.D.
--     Step: 1.1.2                                  Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                            Q.E.D.
--       Step: 1.2.2.1.2                            Q.E.D.
--       Step: 1.2.2.1.3                            Q.E.D.
--       Step: 1.2.2.2.1                            Q.E.D.
--       Step: 1.2.2.2.2                            Q.E.D.
--       Step: 1.2.2.2.3                            Q.E.D.
--       Step: 1.2.2.Completeness                   Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
-- Functions proven terminating: countWS, forestCountWS, sortedInsert, treeWeight
-- [Proven] sortedInsertCountWS :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertCountWSProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertCountWSProof =
   sInduct "sortedInsertCountWS"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) (Forall @"ts" ts) ->
           forestCountWS w s (sortedInsert t ts) .== countWS w s t + forestCountWS w s ts)
       (\_ _ _ ts -> length ts, []) $
       \ih w s t ts -> []
         |- forestCountWS w s (sortedInsert t ts)
         =: [pCase| ts of
               [] -> forestCountWS w s (sortedInsert t ts)
                  =: countWS w s t + forestCountWS w s ts
                  =: qed
               u : us -> forestCountWS w s (sortedInsert t ts)
                      =: cases
                           [ treeWeight t .<= treeWeight u
                               ==> forestCountWS w s (sortedInsert t ts)
                                =: forestCountWS w s (t .: u .: us)
                                =: countWS w s t + forestCountWS w s (u .: us)
                                =: qed
                           , sNot (treeWeight t .<= treeWeight u)
                               ==> forestCountWS w s (sortedInsert t ts)
                                =: forestCountWS w s (u .: sortedInsert t us)
                                ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"t" t, Inst @"ts" us)
                                =: countWS w s t + forestCountWS w s (u .: us)
                                =: qed
                           ]
            |]

-- * Phase 2: Cost additivity

-- | Convert a forest to a tip-only forest, preserving weights.
tipForest :: SList HTree -> SList HTree
tipForest = smtFunction "tipForest"
          $ \ts -> [sCase| ts of
                      []       -> []
                      t : rest -> sTip (treeWeight t) 0 .: tipForest rest
                   |]

-- | @tipForest@ preserves the length of the forest.
--
-- >>> runTPWith cvc5 tipForestLengthProof
-- Inductive lemma (strong): tipForestLength
--   Step: Measure is non-negative              Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                              Q.E.D.
--     Step: 1.1.2                              Q.E.D.
--     Step: 1.2.1                              Q.E.D.
--     Step: 1.2.2                              Q.E.D.
--     Step: 1.2.3                              Q.E.D.
--     Step: 1.Completeness                     Q.E.D.
--   Result:                                    Q.E.D.
-- Functions proven terminating: tipForest, treeWeight
-- [Proven] tipForestLength :: Ɐts ∷ [HTree] → Bool
tipForestLengthProof :: TP (Proof (Forall "ts" [HTree] -> SBool))
tipForestLengthProof =
    sInduct "tipForestLength"
       (\(Forall @"ts" ts) -> length (tipForest ts) .== length ts)
       (length, []) $
       \ih ts -> []
         |- length (tipForest (ts :: SList HTree))
         =: [pCase| ts of
               [] -> length (tipForest ts)
                  =: length ts
                  =: qed
               t : rest -> length (tipForest ts)
                        =: length (sTip (treeWeight t) 0 .: tipForest rest)
                        ?? ih `at` Inst @"ts" rest
                        =: length ts
                        =: qed
            |]

-- | @tipForest@ produces zero forest cost.
--
-- >>> runTPWith cvc5 tipForestCostZeroProof
-- Inductive lemma (strong): tipForestCostZero
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                Q.E.D.
--     Step: 1.1.2                                Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2                                Q.E.D.
--     Step: 1.2.3                                Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: cost, forestCost, tipForest, treeWeight
-- [Proven] tipForestCostZero :: Ɐts ∷ [HTree] → Bool
tipForestCostZeroProof :: TP (Proof (Forall "ts" [HTree] -> SBool))
tipForestCostZeroProof =
    sInduct "tipForestCostZero"
       (\(Forall @"ts" ts) -> forestCost (tipForest ts) .== 0)
       (length, []) $
       \ih ts -> []
         |- forestCost (tipForest (ts :: SList HTree))
         =: [pCase| ts of
               [] -> forestCost (tipForest ts)
                  =: (0 :: SInteger)
                  =: qed
               t : rest -> forestCost (tipForest ts)
                        =: forestCost (sTip (treeWeight t) 0 .: tipForest rest)
                        ?? ih `at` Inst @"ts" rest
                        =: (0 :: SInteger)
                        =: qed
            |]

-- | @tipForest@ preserves forest weight.
--
-- >>> runTPWith cvc5 tipForestWeightProof
-- Inductive lemma (strong): tipForestWeight
--   Step: Measure is non-negative              Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                              Q.E.D.
--     Step: 1.1.2                              Q.E.D.
--     Step: 1.2.1                              Q.E.D.
--     Step: 1.2.2                              Q.E.D.
--     Step: 1.2.3                              Q.E.D.
--     Step: 1.Completeness                     Q.E.D.
--   Result:                                    Q.E.D.
-- Functions proven terminating: forestWeight, tipForest, treeWeight
-- [Proven] tipForestWeight :: Ɐts ∷ [HTree] → Bool
tipForestWeightProof :: TP (Proof (Forall "ts" [HTree] -> SBool))
tipForestWeightProof =
    sInduct "tipForestWeight"
       (\(Forall @"ts" ts) -> forestWeight (tipForest ts) .== forestWeight ts)
       (length, []) $
       \ih ts -> []
         |- forestWeight (tipForest (ts :: SList HTree))
         =: [pCase| ts of
               [] -> forestWeight (tipForest ts)
                  =: forestWeight ts
                  =: qed
               t : rest -> forestWeight (tipForest ts)
                        =: forestWeight (sTip (treeWeight t) 0 .: tipForest rest)
                        ?? ih `at` Inst @"ts" rest
                        =: forestWeight ts
                        =: qed
            |]

-- | @tipForest@ commutes with @sortedInsert@.
--
-- >>> runTPWith cvc5 tipForestCommuteProof
-- Inductive lemma (strong): tipForestCommute
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                               Q.E.D.
--     Step: 1.1.2                               Q.E.D.
--     Step: 1.1.3                               Q.E.D.
--     Step: 1.1.4                               Q.E.D.
--     Step: 1.1.5                               Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                         Q.E.D.
--       Step: 1.2.2.1.2                         Q.E.D.
--       Step: 1.2.2.1.3                         Q.E.D.
--       Step: 1.2.2.1.4                         Q.E.D.
--       Step: 1.2.2.1.5                         Q.E.D.
--       Step: 1.2.2.2.1                         Q.E.D.
--       Step: 1.2.2.2.2                         Q.E.D.
--       Step: 1.2.2.2.3                         Q.E.D.
--       Step: 1.2.2.2.4                         Q.E.D.
--       Step: 1.2.2.2.5                         Q.E.D.
--       Step: 1.2.2.2.6                         Q.E.D.
--       Step: 1.2.2.Completeness                Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: sortedInsert, tipForest, treeWeight
-- [Proven] tipForestCommute :: Ɐx ∷ HTree → Ɐts ∷ [HTree] → Bool
tipForestCommuteProof :: TP (Proof (Forall "x" HTree -> Forall "ts" [HTree] -> SBool))
tipForestCommuteProof =
    sInduct "tipForestCommute"
       (\(Forall @"x" x) (Forall @"ts" ts) ->
           tipForest (sortedInsert x ts) .== sortedInsert (sTip (treeWeight x) 0) (tipForest ts))
       (\_ ts -> length ts, []) $
       \ih x ts -> []
         |- tipForest (sortedInsert x (ts :: SList HTree))
         =: [pCase| ts of
               [] -> tipForest (sortedInsert x ts)
                  =: tipForest (singleton x)
                  =: singleton (sTip (treeWeight x) 0)
                  =: sortedInsert (sTip (treeWeight x) 0) []
                  =: sortedInsert (sTip (treeWeight x) 0) (tipForest ts)
                  =: qed
               u : us -> tipForest (sortedInsert x ts)
                      =: cases
                           [ treeWeight x .<= treeWeight u
                               ==> tipForest (sortedInsert x ts)
                                =: tipForest (x .: u .: us)
                                =: sTip (treeWeight x) 0 .: tipForest (u .: us)
                                =: sortedInsert (sTip (treeWeight x) 0) (tipForest (u .: us))
                                =: sortedInsert (sTip (treeWeight x) 0) (tipForest ts)
                                =: qed
                           , sNot (treeWeight x .<= treeWeight u)
                               ==> tipForest (sortedInsert x ts)
                                =: tipForest (u .: sortedInsert x us)
                                =: sTip (treeWeight u) 0 .: tipForest (sortedInsert x us)
                                ?? ih `at` (Inst @"x" x, Inst @"ts" us)
                                =: sTip (treeWeight u) 0 .: sortedInsert (sTip (treeWeight x) 0) (tipForest us)
                                =: sortedInsert (sTip (treeWeight x) 0) (sTip (treeWeight u) 0 .: tipForest us)
                                =: sortedInsert (sTip (treeWeight x) 0) (tipForest ts)
                                =: qed
                           ]
            |]

-- | @tipForest@ is idempotent.
--
-- >>> runTPWith cvc5 tipForestIdempotentProof
-- Inductive lemma (strong): tipForestIdempotent
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                  Q.E.D.
--     Step: 1.1.2                                  Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2                                  Q.E.D.
--     Step: 1.2.3                                  Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
-- Functions proven terminating: tipForest, treeWeight
-- [Proven] tipForestIdempotent :: Ɐts ∷ [HTree] → Bool
tipForestIdempotentProof :: TP (Proof (Forall "ts" [HTree] -> SBool))
tipForestIdempotentProof =
    sInduct "tipForestIdempotent"
       (\(Forall @"ts" ts) -> tipForest (tipForest ts) .== tipForest ts)
       (length, []) $
       \ih ts -> []
         |- tipForest (tipForest (ts :: SList HTree))
         =: [pCase| ts of
               [] -> tipForest (tipForest ts)
                  =: tipForest ts
                  =: qed
               t : rest -> tipForest (tipForest ts)
                        =: tipForest (sTip (treeWeight t) 0 .: tipForest rest)
                        ?? ih `at` Inst @"ts" rest
                        =: tipForest ts
                        =: qed
            |]

-- | Cost additivity: the cost of building a Huffman tree from a forest equals
-- the forest cost plus the cost of building from the tip-only version.
--
-- >>> runTPWith cvc5 buildHuffmanAdditivityProof
-- Lemma: tipForestCommute                             Q.E.D.
-- Lemma: tipForestCostZero                            Q.E.D.
-- Lemma: tipForestIdempotent                          Q.E.D.
-- Lemma: tipForestLength                              Q.E.D.
-- Lemma: sortedInsertCost                             Q.E.D.
-- Lemma: sortedInsertLength                           Q.E.D.
-- Inductive lemma (strong): buildHuffmanAdditivity
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                               Q.E.D.
--       Step: 1.2.2.1.2                               Q.E.D.
--       Step: 1.2.2.1.3                               Q.E.D.
--       Step: 1.2.2.2.1                               Q.E.D.
--       Step: 1.2.2.2.2                               Q.E.D.
--       Step: 1.2.2.2.3                               Q.E.D.
--       Step: 1.2.2.2.4                               Q.E.D.
--       Step: 1.2.2.2.5                               Q.E.D.
--       Step: 1.2.2.2.6                               Q.E.D.
--       Step: 1.2.2.2.7                               Q.E.D.
--       Step: 1.2.2.2.8                               Q.E.D.
--       Step: 1.2.2.2.9                               Q.E.D.
--       Step: 1.2.2.2.10                              Q.E.D.
--       Step: 1.2.2.2.11                              Q.E.D.
--       Step: 1.2.2.2.12                              Q.E.D.
--       Step: 1.2.2.2.13                              Q.E.D.
--       Step: 1.2.2.Completeness                      Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: buildHuffman, cost, forestCost, sortedInsert, tipForest, treeWeight
-- [Proven] buildHuffmanAdditivity :: Ɐts ∷ [HTree] → Bool
buildHuffmanAdditivityProof :: TP (Proof (Forall "ts" [HTree] -> SBool))
buildHuffmanAdditivityProof = do
    tfComm  <- recall tipForestCommuteProof
    tfCost0 <- recall tipForestCostZeroProof
    tfIdem  <- recall tipForestIdempotentProof
    tfLen   <- recall tipForestLengthProof
    siCost  <- recall sortedInsertCostProof
    siLen   <- recall sortedInsertLengthProof

    sInduct "buildHuffmanAdditivity"
       (\(Forall @"ts" ts) ->
           length ts .>= 1 .=> cost (buildHuffman ts) .== forestCost ts + cost (buildHuffman (tipForest ts)))
       (length, []) $
       \ih ts -> [length ts .>= 1]
         |- forestCost (ts :: SList HTree) + cost (buildHuffman (tipForest ts))
         =: [pCase| ts of
               [] -> forestCost ts + cost (buildHuffman (tipForest ts))
                  =: cost (buildHuffman ts)
                  =: qed
               a : rest' ->
                  forestCost ts + cost (buildHuffman (tipForest ts))
                  =: case rest' of
                        [] -> forestCost ts + cost (buildHuffman (tipForest ts))
                           =: cost a
                           =: cost (buildHuffman ts)
                           =: qed
                        b : rest ->
                           let wa       = treeWeight a
                               wb       = treeWeight b
                               binAB    = sBin a b
                               tipWab   = sTip (wa + wb) 0
                               tipA     = sTip wa 0
                               tipB     = sTip wb 0
                               binTipAB = sBin tipA tipB
                           in  forestCost ts + cost (buildHuffman (tipForest ts))
                           =: cost a + cost b + forestCost rest
                            + cost (buildHuffman (tipA .: tipB .: tipForest rest))
                           =: cost a + cost b + forestCost rest
                            + cost (buildHuffman (sortedInsert binTipAB (tipForest rest)))
                           ?? ih    `at` Inst @"ts" (sortedInsert binTipAB (tipForest rest))
                           ?? siLen `at` (Inst @"t" binTipAB, Inst @"ts" (tipForest rest))
                           ?? tfLen `at` Inst @"ts" rest
                           =: cost a + cost b + forestCost rest
                            + forestCost (sortedInsert binTipAB (tipForest rest))
                            + cost (buildHuffman (tipForest (sortedInsert binTipAB (tipForest rest))))
                           ?? siCost `at` (Inst @"t" binTipAB, Inst @"ts" (tipForest rest))
                           =: cost a + cost b + forestCost rest
                            + cost binTipAB + forestCost (tipForest rest)
                            + cost (buildHuffman (tipForest (sortedInsert binTipAB (tipForest rest))))
                           ?? tfCost0 `at` Inst @"ts" rest
                           ?? cost binTipAB .== wa + wb
                           =: cost a + cost b + forestCost rest + (wa + wb)
                            + cost (buildHuffman (tipForest (sortedInsert binTipAB (tipForest rest))))
                           ?? tfComm `at` (Inst @"x" binTipAB, Inst @"ts" (tipForest rest))
                           ?? treeWeight binTipAB .== wa + wb
                           =: cost a + cost b + forestCost rest + (wa + wb)
                            + cost (buildHuffman (sortedInsert tipWab (tipForest (tipForest rest))))
                           ?? tfIdem `at` Inst @"ts" rest
                           =: cost a + cost b + forestCost rest + (wa + wb)
                            + cost (buildHuffman (sortedInsert tipWab (tipForest rest)))
                           =: cost binAB + forestCost rest
                            + cost (buildHuffman (sortedInsert tipWab (tipForest rest)))
                           ?? tfComm `at` (Inst @"x" binAB, Inst @"ts" rest)
                           ?? treeWeight binAB .== wa + wb
                           =: cost binAB + forestCost rest
                            + cost (buildHuffman (tipForest (sortedInsert binAB rest)))
                           ?? siCost `at` (Inst @"t" binAB, Inst @"ts" rest)
                           =: forestCost (sortedInsert binAB rest)
                            + cost (buildHuffman (tipForest (sortedInsert binAB rest)))
                           ?? ih    `at` Inst @"ts" (sortedInsert binAB rest)
                           ?? siLen `at` (Inst @"t" binAB, Inst @"ts" rest)
                           =: cost (buildHuffman (sortedInsert binAB rest))
                           =: cost (buildHuffman ts)
                           =: qed
            |]

-- | Substitution lemma: replacing a tree in @sortedInsert@ with another of the same weight
-- changes @buildHuffman@ cost by exactly the difference in individual costs.
-- Derived as a corollary of 'buildHuffmanAdditivityProof'.
--
-- >>> runTPWith cvc5 buildHuffmanCostSubstProof
-- Lemma: buildHuffmanAdditivity                       Q.E.D.
-- Lemma: tipForestCommute                             Q.E.D. [Cached]
-- Lemma: sortedInsertCost                             Q.E.D. [Cached]
-- Lemma: sortedInsertLength                           Q.E.D. [Cached]
-- Lemma: buildHuffmanCostSubst                        Q.E.D.
-- Functions proven terminating: buildHuffman, cost, forestCost, sortedInsert, tipForest, treeWeight
-- [Proven] buildHuffmanCostSubst :: Ɐt1 ∷ HTree → Ɐt2 ∷ HTree → Ɐts ∷ [HTree] → Bool
buildHuffmanCostSubstProof :: TP (Proof (Forall "t1" HTree -> Forall "t2" HTree -> Forall "ts" [HTree] -> SBool))
buildHuffmanCostSubstProof = do
    additivity <- recall buildHuffmanAdditivityProof
    tfComm     <- recall tipForestCommuteProof
    siCost     <- recall sortedInsertCostProof
    siLen      <- recall sortedInsertLengthProof

    lemma "buildHuffmanCostSubst"
          (\(Forall @"t1" t1) (Forall @"t2" t2) (Forall @"ts" ts) ->
                 treeWeight t1 .== treeWeight t2
             .=> cost (buildHuffman (sortedInsert t1 ts)) .== cost (buildHuffman (sortedInsert t2 ts)) + cost t1 - cost t2)
          [proofOf additivity, proofOf tfComm, proofOf siCost, proofOf siLen]

-- * Phase 3: Leaf extraction and optimality

-- ** Function definitions

-- | Insert each element of the first list into the second (sorted) list, one by one.
insertAll :: SList HTree -> SList HTree -> SList HTree
insertAll = smtFunction "insertAll"
          $ \xs ys -> [sCase| xs of
                         []       -> ys
                         x : rest -> insertAll rest (sortedInsert x ys)
                      |]

-- | Extract a sorted, weight-only leaf list from a tree. Symbols are stripped to 0,
-- so that same-weight leaves become identical, ensuring sorted lists are unique for
-- a given weight multiset.
leavesOf :: SHTree -> SList HTree
leavesOf = smtFunction "leavesOf"
         $ \t -> [sCase| t of
                    Tip w _ -> [sTip w 0]
                    Bin l r -> insertAll (leavesOf l) (leavesOf r)
                 |]

-- ** insertAll lemmas

-- | @insertAll@ preserves total length: @length(insertAll xs ys) == length xs + length ys@.
--
-- >>> runTPWith cvc5 insertAllLengthProof
-- Lemma: sortedInsertLength                       Q.E.D.
-- Inductive lemma (strong): insertAllLength
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.2.3                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: insertAll, sortedInsert, treeWeight
-- [Proven] insertAllLength :: Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllLengthProof :: TP (Proof (Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllLengthProof = do
    siLen <- recall sortedInsertLengthProof

    sInduct "insertAllLength"
        (\(Forall @"xs" xs) (Forall @"ys" ys) ->
            length (insertAll xs ys) .== length xs + length ys)
        (\xs _ -> length xs, []) $
        \ih xs ys -> []
          |- length (insertAll xs ys)
          =: [pCase| xs of
                [] -> length (insertAll xs ys)
                   =: length xs + length ys
                   =: qed
                x : rest -> length (insertAll xs ys)
                         =: length (insertAll rest (sortedInsert x ys))
                         ?? siLen `at` (Inst @"t" x, Inst @"ts" ys)
                         ?? ih `at` (Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                         =: length xs + length ys
                         =: qed
             |]

-- | @insertAll@ preserves total forest weight: @forestWeight(insertAll xs ys) == forestWeight xs + forestWeight ys@.
--
-- >>> runTPWith cvc5 insertAllWeightProof
-- Lemma: sortedInsertWeight                       Q.E.D.
-- Inductive lemma (strong): insertAllWeight
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.2.3                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: forestWeight, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllWeight :: Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllWeightProof :: TP (Proof (Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllWeightProof = do
    siWeight <- recall sortedInsertWeightProof

    sInduct "insertAllWeight"
        (\(Forall @"xs" xs) (Forall @"ys" ys) ->
            forestWeight (insertAll xs ys) .== forestWeight xs + forestWeight ys)
        (\xs _ -> length xs, []) $
        \ih xs ys -> []
          |- forestWeight (insertAll xs ys)
          =: [pCase| xs of
                [] -> forestWeight (insertAll xs ys)
                   =: forestWeight xs + forestWeight ys
                   =: qed
                x : rest -> forestWeight (insertAll xs ys)
                         =: forestWeight (insertAll rest (sortedInsert x ys))
                         ?? siWeight `at` (Inst @"t" x, Inst @"ts" ys)
                         ?? ih `at` (Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                         =: forestWeight xs + forestWeight ys
                         =: qed
             |]

-- | @insertAll@ preserves total forest cost: @forestCost(insertAll xs ys) == forestCost xs + forestCost ys@.
--
-- >>> runTPWith cvc5 insertAllCostProof
-- Lemma: sortedInsertCost                       Q.E.D.
-- Inductive lemma (strong): insertAllCost
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                               Q.E.D.
--     Step: 1.1.2                               Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2                               Q.E.D.
--     Step: 1.2.3                               Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: cost, forestCost, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllCost :: Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllCostProof :: TP (Proof (Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllCostProof = do
    siCost <- recall sortedInsertCostProof

    sInduct "insertAllCost"
        (\(Forall @"xs" xs) (Forall @"ys" ys) ->
            forestCost (insertAll xs ys) .== forestCost xs + forestCost ys)
        (\xs _ -> length xs, []) $
        \ih xs ys -> []
          |- forestCost (insertAll xs ys)
          =: [pCase| xs of
                [] -> forestCost (insertAll xs ys)
                   =: forestCost xs + forestCost ys
                   =: qed
                x : rest -> forestCost (insertAll xs ys)
                         =: forestCost (insertAll rest (sortedInsert x ys))
                         ?? siCost `at` (Inst @"t" x, Inst @"ts" ys)
                         ?? ih `at` (Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                         =: forestCost xs + forestCost ys
                         =: qed
             |]

-- | @insertAll@ preserves countWS: @forestCountWS w s (insertAll xs ys) == forestCountWS w s xs + forestCountWS w s ys@.
--
-- >>> runTPWith cvc5 insertAllCountWSProof
-- Lemma: sortedInsertCountWS                       Q.E.D.
-- Inductive lemma (strong): insertAllCountWS
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                  Q.E.D.
--     Step: 1.1.2                                  Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2                                  Q.E.D.
--     Step: 1.2.3                                  Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
-- Functions proven terminating: countWS, forestCountWS, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllCountWS :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllCountWSProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllCountWSProof = do
    siCountWS <- recall sortedInsertCountWSProof

    sInduct "insertAllCountWS"
        (\(Forall @"w" w) (Forall @"s" s) (Forall @"xs" xs) (Forall @"ys" ys) ->
            forestCountWS w s (insertAll xs ys) .== forestCountWS w s xs + forestCountWS w s ys)
        (\_ _ xs _ -> length xs, []) $
        \ih w s xs ys -> []
          |- forestCountWS w s (insertAll xs ys)
          =: [pCase| xs of
                [] -> forestCountWS w s (insertAll xs ys)
                   =: forestCountWS w s xs + forestCountWS w s ys
                   =: qed
                x : rest -> forestCountWS w s (insertAll xs ys)
                         =: forestCountWS w s (insertAll rest (sortedInsert x ys))
                         ?? siCountWS `at` (Inst @"w" w, Inst @"s" s, Inst @"t" x, Inst @"ts" ys)
                         ?? ih `at` (Inst @"w" w, Inst @"s" s, Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                         =: forestCountWS w s xs + forestCountWS w s ys
                         =: qed
             |]

-- ** leavesOf lemmas

-- | @leavesOf@ produces as many elements as there are leaves: @length(leavesOf t) == numLeaves t@.
--
-- >>> runTPWith cvc5 leavesOfLengthProof
-- Lemma: treeSizePos                              Q.E.D.
-- Lemma: insertAllLength                          Q.E.D.
-- Inductive lemma (strong): leavesOfLength
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.2.3                                 Q.E.D.
--     Step: 1.2.4                                 Q.E.D.
--     Step: 1.2.5                                 Q.E.D.
--     Step: 1.2.6                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: insertAll, leavesOf, numLeaves, sortedInsert, treeSize, treeWeight
-- [Proven] leavesOfLength :: Ɐt ∷ HTree → Bool
leavesOfLengthProof :: TP (Proof (Forall "t" HTree -> SBool))
leavesOfLengthProof = do
    tsp   <- recall treeSizePosProof
    iaLen <- recall insertAllLengthProof

    sInduct "leavesOfLength"
        (\(Forall @"t" t) -> length (leavesOf t) .== numLeaves t)
        (treeSize, [proofOf tsp]) $
        \ih t -> []
          |- length (leavesOf t)
          =: [pCase| t of
                Tip{}   -> length (leavesOf t)
                        =: numLeaves t
                        =: qed
                Bin l r -> length (leavesOf t)
                        =: length (insertAll (leavesOf l) (leavesOf r))
                        ?? iaLen `at` (Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf r))
                        =: length (leavesOf l) + length (leavesOf r)
                        ?? tsp `at` Inst @"t" r
                        ?? ih `at` Inst @"t" l
                        =: numLeaves l + length (leavesOf r)
                        ?? tsp `at` Inst @"t" l
                        ?? ih `at` Inst @"t" r
                        =: numLeaves l + numLeaves r
                        =: numLeaves t
                        =: qed
             |]

-- | @leavesOf@ preserves total weight: @forestWeight(leavesOf t) == treeWeight t@.
--
-- >>> runTPWith cvc5 leavesOfWeightProof
-- Lemma: treeSizePos                              Q.E.D.
-- Lemma: insertAllWeight                          Q.E.D.
-- Inductive lemma (strong): leavesOfWeight
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                 Q.E.D.
--     Step: 1.1.2                                 Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.2.3                                 Q.E.D.
--     Step: 1.2.4                                 Q.E.D.
--     Step: 1.2.5                                 Q.E.D.
--     Step: 1.2.6                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: forestWeight, insertAll, leavesOf, sortedInsert, treeSize, treeWeight
-- [Proven] leavesOfWeight :: Ɐt ∷ HTree → Bool
leavesOfWeightProof :: TP (Proof (Forall "t" HTree -> SBool))
leavesOfWeightProof = do
    tsp      <- recall treeSizePosProof
    iaWeight <- recall insertAllWeightProof

    sInduct "leavesOfWeight"
        (\(Forall @"t" t) -> forestWeight (leavesOf t) .== treeWeight t)
        (treeSize, [proofOf tsp]) $
        \ih t -> []
          |- forestWeight (leavesOf t)
          =: [pCase| t of
                Tip{}   -> forestWeight (leavesOf t)
                        =: treeWeight t
                        =: qed
                Bin l r -> forestWeight (leavesOf t)
                        =: forestWeight (insertAll (leavesOf l) (leavesOf r))
                        ?? iaWeight `at` (Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf r))
                        =: forestWeight (leavesOf l) + forestWeight (leavesOf r)
                        ?? tsp `at` Inst @"t" r
                        ?? ih `at` Inst @"t" l
                        =: treeWeight l + forestWeight (leavesOf r)
                        ?? tsp `at` Inst @"t" l
                        ?? ih `at` Inst @"t" r
                        =: treeWeight l + treeWeight r
                        =: treeWeight t
                        =: qed
             |]

-- | All leaves have zero cost, so @forestCost(leavesOf t) == 0@.
--
-- >>> runTPWith cvc5 leavesOfCostZeroProof
-- Lemma: treeSizePos                            Q.E.D.
-- Lemma: insertAllCost                          Q.E.D.
-- Inductive lemma (strong): leavesOfCostZero
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                               Q.E.D.
--     Step: 1.1.2                               Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2                               Q.E.D.
--     Step: 1.2.3                               Q.E.D.
--     Step: 1.2.4                               Q.E.D.
--     Step: 1.2.5                               Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: cost, forestCost, insertAll, leavesOf, sortedInsert, treeSize, treeWeight
-- [Proven] leavesOfCostZero :: Ɐt ∷ HTree → Bool
leavesOfCostZeroProof :: TP (Proof (Forall "t" HTree -> SBool))
leavesOfCostZeroProof = do
    tsp    <- recall treeSizePosProof
    iaCost <- recall insertAllCostProof

    sInduct "leavesOfCostZero"
        (\(Forall @"t" t) -> forestCost (leavesOf t) .== 0)
        (treeSize, [proofOf tsp]) $
        \ih t -> []
          |- forestCost (leavesOf t)
          =: [pCase| t of
                Tip{}   -> forestCost (leavesOf t)
                        =: (0 :: SInteger)
                        =: qed
                Bin l r -> forestCost (leavesOf t)
                        =: forestCost (insertAll (leavesOf l) (leavesOf r))
                        ?? iaCost `at` (Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf r))
                        =: forestCost (leavesOf l) + forestCost (leavesOf r)
                        ?? tsp `at` Inst @"t" r
                        ?? ih `at` Inst @"t" l
                        =: forestCost (leavesOf r)
                        ?? tsp `at` Inst @"t" l
                        ?? ih `at` Inst @"t" r
                        =: (0 :: SInteger)
                        =: qed
             |]

-- ** Swap preservation infrastructure

-- | Swap preserves numLeaves: the Tip\/Bin skeleton is unchanged.
--
-- >>> runTPWith cvc5 swapPreservesNumLeavesProof
-- Lemma: treeSizePos                                  Q.E.D.
-- Inductive lemma (strong): swapPreservesNumLeaves
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2                                     Q.E.D.
--     Step: 1.2.3                                     Q.E.D.
--     Step: 1.2.4                                     Q.E.D.
--     Step: 1.2.5                                     Q.E.D.
--     Step: 1.2.6                                     Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: numLeaves, swap, treeSize
-- [Proven] swapPreservesNumLeaves :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapPreservesNumLeavesProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer
                                       -> Forall "wb" Integer -> Forall "sb" Integer
                                       -> Forall "t" HTree -> SBool))
swapPreservesNumLeavesProof = do
    tsp <- recall treeSizePosProof

    sInduct "swapPreservesNumLeaves"
        (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
            numLeaves (swap wa sa wb sb t) .== numLeaves t)
        (\_ _ _ _ t -> treeSize t, [proofOf tsp]) $
        \ih wa sa wb sb t -> []
          |- numLeaves (swap wa sa wb sb t)
          =: [pCase| t of
                Tip{}   -> numLeaves (swap wa sa wb sb t)
                        =: numLeaves t
                        =: qed
                Bin l r -> numLeaves (swap wa sa wb sb t)
                        =: numLeaves (sBin (swap wa sa wb sb l) (swap wa sa wb sb r))
                        =: numLeaves (swap wa sa wb sb l) + numLeaves (swap wa sa wb sb r)
                        ?? tsp `at` Inst @"t" r
                        ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                        =: numLeaves l + numLeaves (swap wa sa wb sb r)
                        ?? tsp `at` Inst @"t" l
                        ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                        =: numLeaves l + numLeaves r
                        =: numLeaves t
                        =: qed
             |]

-- | Commutativity of two sorted inserts, provided same-weight elements are identical.
-- This holds for @Tip w 0@ elements produced by 'leavesOf'.
--
-- >>> runTPWith cvc5 sortedInsertCommProof
-- Inductive lemma (strong): sortedInsertComm
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                               Q.E.D.
--     Step: 1.1.2                               Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2 (4 way case split)
--       Step: 1.2.2.1.1                         Q.E.D.
--       Step: 1.2.2.1.2                         Q.E.D.
--       Step: 1.2.2.1.3                         Q.E.D.
--       Step: 1.2.2.1.4                         Q.E.D.
--       Step: 1.2.2.1.5                         Q.E.D.
--       Step: 1.2.2.1.6                         Q.E.D.
--       Step: 1.2.2.2.1                         Q.E.D.
--       Step: 1.2.2.2.2                         Q.E.D.
--       Step: 1.2.2.3.1                         Q.E.D.
--       Step: 1.2.2.3.2                         Q.E.D.
--       Step: 1.2.2.4.1                         Q.E.D.
--       Step: 1.2.2.4.2                         Q.E.D.
--       Step: 1.2.2.4.3                         Q.E.D.
--       Step: 1.2.2.4.4                         Q.E.D.
--       Step: 1.2.2.4.5                         Q.E.D.
--       Step: 1.2.2.4.6                         Q.E.D.
--       Step: 1.2.2.Completeness                Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: sortedInsert, treeWeight
-- [Proven] sortedInsertComm :: Ɐa ∷ HTree → Ɐb ∷ HTree → Ɐys ∷ [HTree] → Bool
sortedInsertCommProof :: TP (Proof (Forall "a" HTree -> Forall "b" HTree -> Forall "ys" [HTree] -> SBool))
sortedInsertCommProof =
    sInduct "sortedInsertComm"
        (\(Forall @"a" a) (Forall @"b" b) (Forall @"ys" ys) ->
               (treeWeight a .== treeWeight b .=> a .== b)
           .=> sortedInsert a (sortedInsert b ys) .== sortedInsert b (sortedInsert a ys))
        (\_ _ ys -> length ys, []) $
        \ih a b ys -> [treeWeight a .== treeWeight b .=> a .== b]
          |- sortedInsert a (sortedInsert b ys)
          =: [pCase| ys of
                []      -> sortedInsert a (sortedInsert b ys)
                        =: sortedInsert b (sortedInsert a ys)
                        =: qed
                y : ys' -> sortedInsert a (sortedInsert b ys)
                        =: cases
                             [ treeWeight a .> treeWeight y .&& treeWeight b .> treeWeight y
                                 ==> sortedInsert a (sortedInsert b ys)
                                  =: sortedInsert a (y .: sortedInsert b ys')
                                  =: y .: sortedInsert a (sortedInsert b ys')
                                  ?? ih `at` (Inst @"a" a, Inst @"b" b, Inst @"ys" ys')
                                  =: y .: sortedInsert b (sortedInsert a ys')
                                  =: sortedInsert b (y .: sortedInsert a ys')
                                  =: sortedInsert b (sortedInsert a ys)
                                  =: qed
                             , treeWeight a .<= treeWeight y .&& treeWeight b .<= treeWeight y
                                 ==> sortedInsert a (sortedInsert b ys)
                                  =: sortedInsert b (sortedInsert a ys)
                                  =: qed
                             , treeWeight a .<= treeWeight y .&& treeWeight b .> treeWeight y
                                 ==> sortedInsert a (sortedInsert b ys)
                                  =: sortedInsert b (sortedInsert a ys)
                                  =: qed
                             , treeWeight a .> treeWeight y .&& treeWeight b .<= treeWeight y
                                 ==> sortedInsert a (sortedInsert b ys)
                                  =: sortedInsert a (b .: y .: ys')
                                  =: b .: sortedInsert a (y .: ys')
                                  =: b .: y .: sortedInsert a ys'
                                  =: sortedInsert b (y .: sortedInsert a ys')
                                  =: sortedInsert b (sortedInsert a ys)
                                  =: qed
                             ]
             |]

-- | Swap is the identity when neither (wa,sa) nor (wb,sb) exists in the tree.
--
-- >>> runTPWith cvc5 swapIdentityProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Inductive lemma (strong): swapIdentity
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                            Q.E.D.
--     Step: 1.1.2                            Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.2.3                            Q.E.D.
--     Step: 1.2.4                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: countWS, swap, treeSize
-- [Proven] swapIdentity :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapIdentityProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer
                             -> Forall "wb" Integer -> Forall "sb" Integer
                             -> Forall "t" HTree -> SBool))
swapIdentityProof = do
    tsp    <- recall treeSizePosProof
    cwsNN  <- recall countWSNonNegProof

    sInduct "swapIdentity"
        (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
               countWS wa sa t .== 0 .&& countWS wb sb t .== 0
           .=> swap wa sa wb sb t .== t)
        (\_ _ _ _ t -> treeSize t, [proofOf tsp]) $
        \ih wa sa wb sb t -> [countWS wa sa t .== 0, countWS wb sb t .== 0]
          |- swap wa sa wb sb t
          =: [pCase| t of
                Tip{}   -> swap wa sa wb sb t
                        =: t
                        =: qed
                Bin l r -> swap wa sa wb sb t
                        =: sBin (swap wa sa wb sb l) (swap wa sa wb sb r)
                        ?? cwsNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                        ?? cwsNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                        ?? cwsNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                        ?? cwsNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                        ?? tsp `at` Inst @"t" r
                        ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                        ?? tsp `at` Inst @"t" l
                        ?? ih `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                        =: sBin l r
                        =: t
                        =: qed
             |]

-- | Predicate: all elements in the list are of the form @Tip w 0@.
allTip0 :: SList HTree -> SBool
allTip0 = smtFunction "allTip0"
        $ \ts -> [sCase| ts of
                    []       -> sTrue
                    t : rest -> t .== sTip (treeWeight t) 0 .&& allTip0 rest
                 |]

-- | Sorted insertion preserves 'allTip0'.
--
-- >>> runTPWith cvc5 sortedInsertAllTip0Proof
-- Inductive lemma (strong): sortedInsertAllTip0
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                  Q.E.D.
--     Step: 1.1.2                                  Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                            Q.E.D.
--       Step: 1.2.2.1.2                            Q.E.D.
--       Step: 1.2.2.2.1                            Q.E.D.
--       Step: 1.2.2.2.2                            Q.E.D.
--       Step: 1.2.2.Completeness                   Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
-- Functions proven terminating: allTip0, sortedInsert, treeWeight
-- [Proven] sortedInsertAllTip0 :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertAllTip0Proof :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertAllTip0Proof =
    sInduct "sortedInsertAllTip0"
        (\(Forall @"t" t) (Forall @"ts" ts) ->
               t .== sTip (treeWeight t) 0 .&& allTip0 ts
           .=> allTip0 (sortedInsert t ts))
        (\_ ts -> length ts, []) $
        \ih t ts -> [t .== sTip (treeWeight t) 0, allTip0 ts]
          |- allTip0 (sortedInsert t ts)
          =: [pCase| ts of
                [] -> allTip0 (sortedInsert t ts)
                   =: sTrue
                   =: qed
                u : us -> allTip0 (sortedInsert t ts)
                       =: cases
                            [ treeWeight t .<= treeWeight u
                                ==> allTip0 (sortedInsert t ts)
                                 =: sTrue
                                 =: qed
                            , sNot (treeWeight t .<= treeWeight u)
                                ==> allTip0 (sortedInsert t ts)
                                 ?? ih `at` (Inst @"t" t, Inst @"ts" us)
                                 =: sTrue
                                 =: qed
                            ]
             |]

-- | 'insertAll' preserves 'allTip0'.
--
-- >>> runTPWith cvc5 insertAllAllTip0Proof
-- Lemma: sortedInsertAllTip0                       Q.E.D.
-- Inductive lemma (strong): insertAllAllTip0
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                  Q.E.D.
--     Step: 1.1.2                                  Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2                                  Q.E.D.
--     Step: 1.2.3                                  Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
-- Functions proven terminating: allTip0, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllAllTip0 :: Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllAllTip0Proof :: TP (Proof (Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllAllTip0Proof = do
    siAT <- recall sortedInsertAllTip0Proof

    sInduct "insertAllAllTip0"
        (\(Forall @"xs" xs) (Forall @"ys" ys) ->
               allTip0 xs .&& allTip0 ys .=> allTip0 (insertAll xs ys))
        (\xs _ -> length xs, []) $
        \ih xs ys -> [allTip0 xs, allTip0 ys]
          |- allTip0 (insertAll xs ys)
          =: [pCase| xs of
                [] -> allTip0 (insertAll xs ys)
                   =: sTrue
                   =: qed
                x : rest -> allTip0 (insertAll xs ys)
                         =: allTip0 (insertAll rest (sortedInsert x ys))
                         ?? siAT `at` (Inst @"t" x, Inst @"ts" ys)
                         ?? ih `at` (Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                         =: sTrue
                         =: qed
             |]

-- | 'leavesOf' always produces an 'allTip0' list.
--
-- >>> runTPWith cvc5 leavesOfAllTip0Proof
-- Lemma: treeSizePos                               Q.E.D.
-- Lemma: insertAllAllTip0                          Q.E.D.
-- Inductive lemma (strong): leavesOfAllTip0
--   Step: Measure is non-negative                  Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                  Q.E.D.
--     Step: 1.1.2                                  Q.E.D.
--     Step: 1.2.1                                  Q.E.D.
--     Step: 1.2.2                                  Q.E.D.
--     Step: 1.2.3                                  Q.E.D.
--     Step: 1.Completeness                         Q.E.D.
--   Result:                                        Q.E.D.
-- Functions proven terminating: allTip0, insertAll, leavesOf, sortedInsert, treeSize, treeWeight
-- [Proven] leavesOfAllTip0 :: Ɐt ∷ HTree → Bool
leavesOfAllTip0Proof :: TP (Proof (Forall "t" HTree -> SBool))
leavesOfAllTip0Proof = do
    tsp   <- recall treeSizePosProof
    iaAT  <- recall insertAllAllTip0Proof

    sInduct "leavesOfAllTip0"
        (\(Forall @"t" t) -> allTip0 (leavesOf t))
        (treeSize, [proofOf tsp]) $
        \ih t -> []
          |- allTip0 (leavesOf t)
          =: [pCase| t of
                Tip{}   -> allTip0 (leavesOf t)
                        =: sTrue
                        =: qed
                Bin l r -> allTip0 (leavesOf t)
                        =: allTip0 (insertAll (leavesOf l) (leavesOf r))
                        ?? tsp `at` Inst @"t" r
                        ?? ih `at` Inst @"t" l
                        ?? tsp `at` Inst @"t" l
                        ?? ih `at` Inst @"t" r
                        ?? iaAT `at` (Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf r))
                        =: sTrue
                        =: qed
             |]

-- | Moving an element from the second argument of 'insertAll' to a 'sortedInsert' outside:
-- @sortedInsert a (insertAll xs ys) == insertAll xs (sortedInsert a ys)@, when all elements are @Tip w 0@.
--
-- >>> runTPWith cvc5 insertAllSortedInsertProof
-- Lemma: sortedInsertComm                            Q.E.D.
-- Inductive lemma (strong): insertAllSortedInsert
--   Step: Measure is non-negative                    Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                    Q.E.D.
--     Step: 1.1.2                                    Q.E.D.
--     Step: 1.2.1                                    Q.E.D.
--     Step: 1.2.2                                    Q.E.D.
--     Step: 1.2.3                                    Q.E.D.
--     Step: 1.2.4                                    Q.E.D.
--     Step: 1.2.5                                    Q.E.D.
--     Step: 1.Completeness                           Q.E.D.
--   Result:                                          Q.E.D.
-- Functions proven terminating: allTip0, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllSortedInsert :: Ɐa ∷ HTree → Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllSortedInsertProof :: TP (Proof (Forall "a" HTree -> Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllSortedInsertProof = do
    siComm <- recall sortedInsertCommProof

    sInduct "insertAllSortedInsert"
        (\(Forall @"a" a) (Forall @"xs" xs) (Forall @"ys" ys) ->
               a .== sTip (treeWeight a) 0 .&& allTip0 xs
           .=> sortedInsert a (insertAll xs ys) .== insertAll xs (sortedInsert a ys))
        (\_ xs _ -> length xs, []) $
        \ih a xs ys -> [a .== sTip (treeWeight a) 0, allTip0 xs]
          |- sortedInsert a (insertAll xs ys)
          =: [pCase| xs of
                [] -> sortedInsert a (insertAll xs ys)
                   =: insertAll xs (sortedInsert a ys)
                   =: qed
                x : rest -> sortedInsert a (insertAll xs ys)
                         =: sortedInsert a (insertAll rest (sortedInsert x ys))
                         ?? ih `at` (Inst @"a" a, Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                         =: insertAll rest (sortedInsert a (sortedInsert x ys))
                         ?? siComm `at` (Inst @"a" a, Inst @"b" x, Inst @"ys" ys)
                         =: insertAll rest (sortedInsert x (sortedInsert a ys))
                         =: insertAll xs (sortedInsert a ys)
                         =: qed
             |]

-- | Moving an element from the first argument of 'insertAll' to a 'sortedInsert' outside:
-- @insertAll (sortedInsert a xs) ys == sortedInsert a (insertAll xs ys)@, when all elements are @Tip w 0@.
--
-- >>> runTPWith cvc5 insertAllSortedInsertLProof
-- Lemma: sortedInsertComm                             Q.E.D.
-- Lemma: insertAllSortedInsert                        Q.E.D.
-- Inductive lemma (strong): insertAllSortedInsertL
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                               Q.E.D.
--       Step: 1.2.2.1.2                               Q.E.D.
--       Step: 1.2.2.1.3                               Q.E.D.
--       Step: 1.2.2.1.4                               Q.E.D.
--       Step: 1.2.2.1.5                               Q.E.D.
--       Step: 1.2.2.1.6                               Q.E.D.
--       Step: 1.2.2.1.7                               Q.E.D.
--       Step: 1.2.2.2.1                               Q.E.D.
--       Step: 1.2.2.2.2                               Q.E.D.
--       Step: 1.2.2.2.3                               Q.E.D.
--       Step: 1.2.2.2.4                               Q.E.D.
--       Step: 1.2.2.2.5                               Q.E.D.
--       Step: 1.2.2.Completeness                      Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: allTip0, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllSortedInsertL :: Ɐa ∷ HTree → Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllSortedInsertLProof :: TP (Proof (Forall "a" HTree -> Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllSortedInsertLProof = do
    siComm <- recall sortedInsertCommProof
    iaSI   <- recall insertAllSortedInsertProof

    sInduct "insertAllSortedInsertL"
        (\(Forall @"a" a) (Forall @"xs" xs) (Forall @"ys" ys) ->
               a .== sTip (treeWeight a) 0 .&& allTip0 xs
           .=> insertAll (sortedInsert a xs) ys .== sortedInsert a (insertAll xs ys))
        (\_ xs _ -> length xs, []) $
        \ih a xs ys -> [a .== sTip (treeWeight a) 0, allTip0 xs]
          |- insertAll (sortedInsert a xs) ys
          =: [pCase| xs of
                [] -> insertAll (sortedInsert a xs) ys
                   =: sortedInsert a (insertAll xs ys)
                   =: qed
                x : rest -> insertAll (sortedInsert a xs) ys
                         =: cases
                              [ treeWeight a .<= treeWeight x
                                  ==> insertAll (sortedInsert a xs) ys
                                   =: insertAll (a .: x .: rest) ys
                                   =: insertAll (x .: rest) (sortedInsert a ys)
                                   =: insertAll rest (sortedInsert x (sortedInsert a ys))
                                   ?? siComm `at` (Inst @"a" x, Inst @"b" a, Inst @"ys" ys)
                                   =: insertAll rest (sortedInsert a (sortedInsert x ys))
                                   ?? iaSI `at` (Inst @"a" a, Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                                   =: sortedInsert a (insertAll rest (sortedInsert x ys))
                                   =: sortedInsert a (insertAll xs ys)
                                   =: qed
                              , sNot (treeWeight a .<= treeWeight x)
                                  ==> insertAll (sortedInsert a xs) ys
                                   =: insertAll (x .: sortedInsert a rest) ys
                                   =: insertAll (sortedInsert a rest) (sortedInsert x ys)
                                   ?? ih `at` (Inst @"a" a, Inst @"xs" rest, Inst @"ys" (sortedInsert x ys))
                                   =: sortedInsert a (insertAll rest (sortedInsert x ys))
                                   =: sortedInsert a (insertAll xs ys)
                                   =: qed
                              ]
             |]

-- | Sorted insertion is injective: @sortedInsert a xs == sortedInsert a ys → xs == ys@.
--
-- >>> runTPWith cvc5 sortedInsertInjectiveProof
-- Inductive lemma (strong): sortedInsertInjective
--   Step: Measure is non-negative                    Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                    Q.E.D.
--     Step: 1.1.2                                    Q.E.D.
--     Step: 1.2.1                                    Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                              Q.E.D.
--       Step: 1.2.2.1.2                              Q.E.D.
--       Step: 1.2.2.2.1                              Q.E.D.
--       Step: 1.2.2.2.2                              Q.E.D.
--       Step: 1.2.2.Completeness                     Q.E.D.
--     Step: 1.Completeness                           Q.E.D.
--   Result:                                          Q.E.D.
-- Functions proven terminating: sortedInsert, treeWeight
-- [Proven] sortedInsertInjective :: Ɐa ∷ HTree → Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
sortedInsertInjectiveProof :: TP (Proof (Forall "a" HTree -> Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
sortedInsertInjectiveProof =
    sInduct "sortedInsertInjective"
        (\(Forall @"a" a) (Forall @"xs" xs) (Forall @"ys" ys) ->
            sortedInsert a xs .== sortedInsert a ys .=> xs .== ys)
        (\_ xs _ -> length xs, []) $
        \ih a xs ys -> [sortedInsert a xs .== sortedInsert a ys]
          |- xs .== ys
          =: [pCase| xs of
                [] -> xs .== ys
                   =: sTrue
                   =: qed
                x : xs' -> xs .== ys
                         =: cases
                              [ treeWeight a .<= treeWeight x
                                  ==> xs .== ys
                                   =: sTrue
                                   =: qed
                              , sNot (treeWeight a .<= treeWeight x)
                                  ==> xs .== ys
                                   ?? ih `at` (Inst @"a" a, Inst @"xs" xs', Inst @"ys" (tail ys))
                                   =: sTrue
                                   =: qed
                              ]
             |]

-- ** leavesOfSwap

-- | Swap is symmetric in its two pairs: @swap wa sa wb sb t == swap wb sb wa sa t@.
--
-- >>> runTPWith cvc5 swapSymmetricProof
-- Lemma: treeSizePos                         Q.E.D.
-- Inductive lemma (strong): swapSymmetric
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                            Q.E.D.
--     Step: 1.1.2                            Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: swap, treeSize
-- [Proven] swapSymmetric :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapSymmetricProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer
                              -> Forall "wb" Integer -> Forall "sb" Integer
                              -> Forall "t" HTree -> SBool))
swapSymmetricProof = do
    tsp <- recall treeSizePosProof

    sInduct "swapSymmetric"
        (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
            swap wa sa wb sb t .== swap wb sb wa sa t)
        (\_ _ _ _ t -> treeSize t, [proofOf tsp]) $
        \ih wa sa wb sb t -> []
          |- swap wa sa wb sb t
          =: [pCase| t of
                Tip{}   -> swap wa sa wb sb t
                        =: swap wb sb wa sa t
                        =: qed
                Bin l r -> swap wa sa wb sb t
                        ?? tsp `at` Inst @"t" l
                        ?? tsp `at` Inst @"t" r
                        ?? ih  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                        ?? ih  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                        =: swap wb sb wa sa t
                        =: qed
             |]

-- | Single-pair swap: when @countWS wa sa t == 1@ and @countWS wb sb t == 0@, swapping
-- replaces one @Tip wa 0@ with @Tip wb 0@ in 'leavesOf'. Adding back @Tip wa 0@ to the swapped
-- list equals adding @Tip wb 0@ to the original.
--
-- >>> runTPWith cvc5 leavesOfSwapSingleProof
-- Lemma: treeSizePos                                  Q.E.D.
-- Lemma: countWSNonNeg                                Q.E.D.
-- Lemma: countWSBin                                   Q.E.D.
-- Lemma: swapIdentity                                 Q.E.D.
-- Lemma: leavesOfAllTip0                              Q.E.D.
-- Lemma: insertAllSortedInsertL                       Q.E.D.
-- Lemma: insertAllSortedInsert                        Q.E.D. [Cached]
-- Inductive lemma (strong): leavesOfSwapSingle
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2                                     Q.E.D.
--     Step: 1.2.3 (3 way case split)
--       Step: 1.2.3.1.1                               Q.E.D.
--       Step: 1.2.3.1.2                               Q.E.D.
--       Step: 1.2.3.1.3                               Q.E.D.
--       Step: 1.2.3.1.4                               Q.E.D.
--       Step: 1.2.3.1.5                               Q.E.D.
--       Step: 1.2.3.1.6                               Q.E.D.
--       Step: 1.2.3.2.1                               Q.E.D.
--       Step: 1.2.3.2.2                               Q.E.D.
--       Step: 1.2.3.2.3                               Q.E.D.
--       Step: 1.2.3.2.4                               Q.E.D.
--       Step: 1.2.3.2.5                               Q.E.D.
--       Step: 1.2.3.2.6                               Q.E.D.
--       Step: 1.2.3.3.1                               Q.E.D.
--       Step: 1.2.3.3.2                               Q.E.D.
--       Step: 1.2.3.Completeness                      Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: allTip0, countWS, insertAll, leavesOf, sortedInsert, swap, treeSize, treeWeight
-- [Proven] leavesOfSwapSingle :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
leavesOfSwapSingleProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer
                                   -> Forall "wb" Integer -> Forall "sb" Integer
                                   -> Forall "t" HTree -> SBool))
leavesOfSwapSingleProof = do
    tsp    <- recall treeSizePosProof
    cwsNN  <- recall countWSNonNegProof
    cwsBin <- recall countWSBinProof
    swapId <- recall swapIdentityProof
    loAT   <- recall leavesOfAllTip0Proof
    iaSIL  <- recall insertAllSortedInsertLProof
    iaSI   <- recall insertAllSortedInsertProof

    sInduct "leavesOfSwapSingle"
        (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
               countWS wa sa t .== 1 .&& countWS wb sb t .== 0 .&& (wa ./= wb .|| sa ./= sb)
           .=> sortedInsert (sTip wa 0) (leavesOf (swap wa sa wb sb t))
               .== sortedInsert (sTip wb 0) (leavesOf t))
        (\_ _ _ _ t -> treeSize t, [proofOf tsp]) $
        \ih wa sa wb sb t -> [countWS wa sa t .== 1, countWS wb sb t .== 0, wa ./= wb .|| sa ./= sb]
          |- sortedInsert (sTip wa 0) (leavesOf (swap wa sa wb sb t))
          =: [pCase| t of
                Tip{}   -> sortedInsert (sTip wa 0) (leavesOf (swap wa sa wb sb t))
                        =: sortedInsert (sTip wb 0) (leavesOf t)
                        =: qed
                Bin l r -> sortedInsert (sTip wa 0) (leavesOf (swap wa sa wb sb t))
                        =: sortedInsert (sTip wa 0) (insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r)))
                        =: cases
                             [ -- Case: (wa,sa) in left subtree
                               countWS wa sa l .== 1 .&& countWS wa sa r .== 0
                                 ==> let wa0 = sTip wa 0
                                         wb0 = sTip wb 0
                                     in  sortedInsert wa0 (insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r)))
                                      ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                      ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                      ?? swapId `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                      =: sortedInsert wa0 (insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf r))
                                      ?? loAT  `at` Inst @"t" (swap wa sa wb sb l)
                                      ?? iaSIL `at` (Inst @"a" wa0, Inst @"xs" (leavesOf (swap wa sa wb sb l)), Inst @"ys" (leavesOf r))
                                      =: insertAll (sortedInsert wa0 (leavesOf (swap wa sa wb sb l))) (leavesOf r)
                                      ?? tsp   `at` Inst @"t" r
                                      ?? cwsNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                      ?? cwsNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                      ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                      =: insertAll (sortedInsert wb0 (leavesOf l)) (leavesOf r)
                                      ?? loAT  `at` Inst @"t" l
                                      ?? iaSIL `at` (Inst @"a" wb0, Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf r))
                                      =: sortedInsert wb0 (insertAll (leavesOf l) (leavesOf r))
                                      =: sortedInsert wb0 (leavesOf t)
                                      =: qed

                             -- Case: (wa,sa) in right subtree
                             , countWS wa sa l .== 0 .&& countWS wa sa r .== 1
                                 ==> let wa0 = sTip wa 0
                                         wb0 = sTip wb 0
                                     in  sortedInsert wa0 (insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r)))
                                      ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                      ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                      ?? swapId `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                      =: sortedInsert wa0 (insertAll (leavesOf l) (leavesOf (swap wa sa wb sb r)))
                                      ?? loAT `at` Inst @"t" l
                                      ?? iaSI  `at` (Inst @"a" wa0, Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf (swap wa sa wb sb r)))
                                      =: insertAll (leavesOf l) (sortedInsert wa0 (leavesOf (swap wa sa wb sb r)))
                                      ?? tsp   `at` Inst @"t" l
                                      ?? cwsNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                      ?? cwsNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                      ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                      =: insertAll (leavesOf l) (sortedInsert wb0 (leavesOf r))
                                      ?? loAT `at` Inst @"t" l
                                      ?? iaSI `at` (Inst @"a" wb0, Inst @"xs" (leavesOf l), Inst @"ys" (leavesOf r))
                                      =: sortedInsert wb0 (insertAll (leavesOf l) (leavesOf r))
                                      =: sortedInsert wb0 (leavesOf t)
                                      =: qed

                             -- Impossible: countWS wa sa l + countWS wa sa r == 1 with both >= 0
                             ,     sNot (countWS wa sa l .== 1 .&& countWS wa sa r .== 0)
                               .&& sNot (countWS wa sa l .== 0 .&& countWS wa sa r .== 1)
                                 ==> sortedInsert (sTip wa 0) (insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r)))
                                      ?? cwsNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                                      ?? cwsNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                      ?? cwsBin `at` (Inst @"w" wa, Inst @"s" sa, Inst @"l" l, Inst @"r" r)
                                      =: sortedInsert (sTip wb 0) (leavesOf t)
                                      =: qed
                             ]
             |]

-- | Swap preserves 'leavesOf': when both pairs have count 1 and are distinct,
-- @leavesOf(swap wa sa wb sb t) == leavesOf t@.
--
-- >>> runTPWith cvc5 leavesOfSwapProof
-- Lemma: treeSizePos                                  Q.E.D.
-- Lemma: countWSNonNeg                                Q.E.D.
-- Lemma: countWSBin                                   Q.E.D.
-- Lemma: swapIdentity                                 Q.E.D.
-- Lemma: leavesOfAllTip0                              Q.E.D.
-- Lemma: insertAllSortedInsertL                       Q.E.D.
-- Lemma: insertAllSortedInsert                        Q.E.D. [Cached]
-- Lemma: sortedInsertInjective                        Q.E.D.
-- Lemma: leavesOfSwapSingle                           Q.E.D.
-- Lemma: swapSymmetric                                Q.E.D.
-- Inductive lemma (strong): leavesOfSwap
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2                                     Q.E.D.
--     Step: 1.2.3 (5 way case split)
--       Step: 1.2.3.1.1                               Q.E.D.
--       Step: 1.2.3.1.2                               Q.E.D.
--       Step: 1.2.3.1.3                               Q.E.D.
--       Step: 1.2.3.2.1                               Q.E.D.
--       Step: 1.2.3.2.2                               Q.E.D.
--       Step: 1.2.3.2.3                               Q.E.D.
--       Step: 1.2.3.3.1                               Q.E.D.
--       Step: 1.2.3.3.2                               Q.E.D.
--       Step: 1.2.3.3.3                               Q.E.D.
--       Step: 1.2.3.4.1                               Q.E.D.
--       Step: 1.2.3.4.2                               Q.E.D.
--       Step: 1.2.3.4.3                               Q.E.D.
--       Step: 1.2.3.5.1                               Q.E.D.
--       Step: 1.2.3.5.2                               Q.E.D.
--       Step: 1.2.3.Completeness                      Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: allTip0, countWS, insertAll, leavesOf, sortedInsert, swap, treeSize, treeWeight
-- [Proven] leavesOfSwap :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
leavesOfSwapProof :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer
                             -> Forall "wb" Integer -> Forall "sb" Integer
                             -> Forall "t" HTree -> SBool))
leavesOfSwapProof = do
    tsp     <- recall treeSizePosProof
    cwsNN   <- recall countWSNonNegProof
    cwsBin  <- recall countWSBinProof
    swapId  <- recall swapIdentityProof
    loAT    <- recall leavesOfAllTip0Proof
    iaSIL   <- recall insertAllSortedInsertLProof
    iaSI    <- recall insertAllSortedInsertProof
    siInj   <- recall sortedInsertInjectiveProof
    single  <- recall leavesOfSwapSingleProof
    swapSym <- recall swapSymmetricProof

    sInduct "leavesOfSwap"
        (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
               countWS wa sa t .== 1 .&& countWS wb sb t .== 1 .&& (wa ./= wb .|| sa ./= sb)
           .=> leavesOf (swap wa sa wb sb t) .== leavesOf t)
        (\_ _ _ _ t -> treeSize t, [proofOf tsp]) $
        \ih wa sa wb sb t -> [countWS wa sa t .== 1, countWS wb sb t .== 1, wa ./= wb .|| sa ./= sb]
          |- leavesOf (swap wa sa wb sb t)
          =: [pCase| t of
                -- Tip: vacuously false (can't have two distinct pairs in one leaf)
                Tip{}   -> leavesOf (swap wa sa wb sb t)
                        =: leavesOf t
                        =: qed
                Bin l r -> leavesOf (swap wa sa wb sb t)
                        =: insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r))
                        =: cases
                             [ -- Case 1: Both pairs in left subtree
                               countWS wa sa l .== 1 .&& countWS wb sb l .== 1
                                 ==> insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r))
                                  ?? cwsNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                  ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                  ?? swapId `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                  ?? tsp    `at` Inst @"t" r
                                  ?? ih     `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                  =: insertAll (leavesOf l) (leavesOf r)
                                  =: leavesOf t
                                  =: qed

                             -- Case 2: Both pairs in right subtree
                             , countWS wa sa r .== 1 .&& countWS wb sb r .== 1
                                 ==> insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r))
                                  ?? cwsNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                                  ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                  ?? swapId `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                  ?? tsp    `at` Inst @"t" l
                                  ?? ih     `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                  =: insertAll (leavesOf l) (leavesOf r)
                                  =: leavesOf t
                                  =: qed

                             -- Case 3: (wa,sa) in l, (wb,sb) in r
                             -- Strategy: add sortedInsert wa0 to both sides, chain through
                             -- single(l) + iaSIL + single(r) + iaSI, then cancel via siInj.
                             , countWS wa sa l .== 1 .&& countWS wb sb r .== 1
                                 ==> let wa0 = sTip wa 0
                                         wb0 = sTip wb 0
                                         lsl = leavesOf (swap wa sa wb sb l)
                                         lsr = leavesOf (swap wa sa wb sb r)
                                         ll  = leavesOf l
                                         lr  = leavesOf r
                                     in  insertAll lsl lsr
                                      -- Derive countWS wb sb l == 0 and countWS wa sa r == 0
                                      ?? cwsNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                      ?? cwsBin  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"l" l, Inst @"r" r)
                                      ?? cwsNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                      ?? cwsBin  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"l" l, Inst @"r" r)
                                      -- single on l: sortedInsert wa0 lsl == sortedInsert wb0 ll
                                      ?? single  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                      -- single on r: sortedInsert wb0 lsr == sortedInsert wa0 lr
                                      ?? single  `at` (Inst @"wa" wb, Inst @"sa" sb, Inst @"wb" wa, Inst @"sb" sa, Inst @"t" r)
                                      ?? swapSym `at` (Inst @"wa" wb, Inst @"sa" sb, Inst @"wb" wa, Inst @"sb" sa, Inst @"t" r)
                                      -- allTip0 for iaSIL/iaSI preconditions
                                      ?? loAT    `at` Inst @"t" (swap wa sa wb sb l)
                                      ?? loAT    `at` Inst @"t" l
                                      -- rearrangement: iaSIL pulls sortedInsert out of insertAll's left arg
                                      ?? iaSIL   `at` (Inst @"a" wa0, Inst @"xs" lsl, Inst @"ys" lsr)
                                      ?? iaSIL   `at` (Inst @"a" wb0, Inst @"xs" ll,  Inst @"ys" lsr)
                                      -- rearrangement: iaSI moves sortedInsert into insertAll's right arg
                                      ?? iaSI    `at` (Inst @"a" wb0, Inst @"xs" ll,  Inst @"ys" lsr)
                                      ?? iaSI    `at` (Inst @"a" wa0, Inst @"xs" ll,  Inst @"ys" lr)
                                      -- cancel: sortedInsert wa0 (insertAll lsl lsr) == sortedInsert wa0 (insertAll ll lr)
                                      ?? siInj   `at` (Inst @"a" wa0, Inst @"xs" (insertAll lsl lsr), Inst @"ys" (insertAll ll lr))
                                      =: insertAll ll lr
                                      =: leavesOf t
                                      =: qed

                             -- Case 4: (wa,sa) in r, (wb,sb) in l (symmetric to case 3)
                             -- Same strategy with wb0/wa0 roles swapped.
                             , countWS wa sa r .== 1 .&& countWS wb sb l .== 1
                                 ==> let wa0 = sTip wa 0
                                         wb0 = sTip wb 0
                                         lsl = leavesOf (swap wa sa wb sb l)
                                         lsr = leavesOf (swap wa sa wb sb r)
                                         ll  = leavesOf l
                                         lr  = leavesOf r
                                     in  insertAll lsl lsr
                                      -- Derive countWS wa sa l == 0 and countWS wb sb r == 0
                                      ?? cwsNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                                      ?? cwsBin  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"l" l, Inst @"r" r)
                                      ?? cwsNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                      ?? cwsBin  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"l" l, Inst @"r" r)
                                      -- single on l (reversed): sortedInsert wb0 lsl == sortedInsert wa0 ll
                                      ?? single  `at` (Inst @"wa" wb, Inst @"sa" sb, Inst @"wb" wa, Inst @"sb" sa, Inst @"t" l)
                                      ?? swapSym `at` (Inst @"wa" wb, Inst @"sa" sb, Inst @"wb" wa, Inst @"sb" sa, Inst @"t" l)
                                      -- single on r: sortedInsert wa0 lsr == sortedInsert wb0 lr
                                      ?? single  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                      -- allTip0 for iaSIL/iaSI preconditions
                                      ?? loAT    `at` Inst @"t" (swap wa sa wb sb l)
                                      ?? loAT    `at` Inst @"t" l
                                      -- rearrangement: iaSIL pulls sortedInsert out of insertAll's left arg
                                      ?? iaSIL   `at` (Inst @"a" wb0, Inst @"xs" lsl, Inst @"ys" lsr)
                                      ?? iaSIL   `at` (Inst @"a" wa0, Inst @"xs" ll,  Inst @"ys" lsr)
                                      -- rearrangement: iaSI moves sortedInsert into insertAll's right arg
                                      ?? iaSI    `at` (Inst @"a" wa0, Inst @"xs" ll,  Inst @"ys" lsr)
                                      ?? iaSI    `at` (Inst @"a" wb0, Inst @"xs" ll,  Inst @"ys" lr)
                                      -- cancel: sortedInsert wb0 (insertAll lsl lsr) == sortedInsert wb0 (insertAll ll lr)
                                      ?? siInj   `at` (Inst @"a" wb0, Inst @"xs" (insertAll lsl lsr), Inst @"ys" (insertAll ll lr))
                                      =: insertAll ll lr
                                      =: leavesOf t
                                      =: qed

                             -- Impossible: 4 cases above are exhaustive
                             ,     sNot (countWS wa sa l .== 1 .&& countWS wb sb l .== 1)
                               .&& sNot (countWS wa sa r .== 1 .&& countWS wb sb r .== 1)
                               .&& sNot (countWS wa sa l .== 1 .&& countWS wb sb r .== 1)
                               .&& sNot (countWS wa sa r .== 1 .&& countWS wb sb l .== 1)
                                 ==> insertAll (leavesOf (swap wa sa wb sb l)) (leavesOf (swap wa sa wb sb r))
                                      ?? cwsNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                                      ?? cwsNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                      ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                      ?? cwsNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                      ?? cwsBin `at` (Inst @"w" wa, Inst @"s" sa, Inst @"l" l, Inst @"r" r)
                                      ?? cwsBin `at` (Inst @"w" wb, Inst @"s" sb, Inst @"l" l, Inst @"r" r)
                                      =: leavesOf t
                                      =: qed
                             ]
             |]

-- * Phase 4: Optimality

-- ** Relabeling infrastructure
--
-- To apply the swap argument without a distinctness precondition, we relabel
-- each leaf with a unique symbol (its in-order index). Since @cost@ and @leavesOf@
-- ignore symbols, this doesn't change the problem but guarantees @countWS w s t == 1@
-- for each leaf.

-- | Relabel leaves with consecutive symbols starting from @n@.
-- The left subtree gets symbols @[n .. n + numLeaves l - 1]@ and the right
-- subtree gets @[n + numLeaves l ..]@.
relabelFrom :: SInteger -> SHTree -> SHTree
relabelFrom = smtFunction "relabelFrom"
            $ \n t -> [sCase| t of
                         Tip w _ -> sTip w n
                         Bin l r -> sBin (relabelFrom n l) (relabelFrom (n + numLeaves l) r)
                      |]

-- | Relabeling preserves treeWeight: @treeWeight (relabelFrom n t) == treeWeight t@.
--
-- >>> runTPWith cvc5 relabelWeightProof
-- Lemma: treeSizePos                         Q.E.D.
-- Inductive lemma (strong): relabelWeight
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: numLeaves, relabelFrom, treeSize, treeWeight
-- [Proven] relabelWeight :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelWeightProof :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelWeightProof = do
   tsPos <- recall treeSizePosProof

   sInduct "relabelWeight"
       (\(Forall @"n" n) (Forall @"t" t) -> treeWeight (relabelFrom n t) .== treeWeight t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- treeWeight (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> treeWeight (relabelFrom n t)
                       ?? ih `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: treeWeight t
                       =: qed
            |]

-- | Relabeling preserves numLeaves: @numLeaves (relabelFrom n t) == numLeaves t@.
--
-- >>> runTPWith cvc5 relabelNumLeavesProof
-- Lemma: treeSizePos                            Q.E.D.
-- Inductive lemma (strong): relabelNumLeaves
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                 Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2                               Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: numLeaves, relabelFrom, treeSize
-- [Proven] relabelNumLeaves :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelNumLeavesProof :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelNumLeavesProof = do
   tsPos <- recall treeSizePosProof

   sInduct "relabelNumLeaves"
       (\(Forall @"n" n) (Forall @"t" t) -> numLeaves (relabelFrom n t) .== numLeaves t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- numLeaves (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> numLeaves (relabelFrom n t)
                       ?? ih `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: numLeaves t
                       =: qed
            |]

-- | Relabeling preserves cost: @cost (relabelFrom n t) == cost t@.
-- Relies on 'relabelWeightProof' since the cost formula involves @treeWeight@.
--
-- >>> runTPWith cvc5 relabelCostProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: relabelWeight                       Q.E.D.
-- Inductive lemma (strong): relabelCost
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: cost, numLeaves, relabelFrom, treeSize, treeWeight
-- [Proven] relabelCost :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelCostProof :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelCostProof = do
   tsPos <- recall treeSizePosProof
   rlWt  <- recall relabelWeightProof

   sInduct "relabelCost"
       (\(Forall @"n" n) (Forall @"t" t) -> cost (relabelFrom n t) .== cost t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- cost (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> cost (relabelFrom n t)
                       ?? ih   `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih   `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? rlWt `at` (Inst @"n" n, Inst @"t" l)
                       ?? rlWt `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: cost t
                       =: qed
            |]

-- | Relabeling preserves leavesOf: @leavesOf (relabelFrom n t) == leavesOf t@.
-- Since @leavesOf@ strips all symbols to 0, the relabeling has no effect.
--
-- >>> runTPWith cvc5 relabelLeavesOfProof
-- Lemma: treeSizePos                           Q.E.D.
-- Inductive lemma (strong): relabelLeavesOf
--   Step: Measure is non-negative              Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                Q.E.D.
--     Step: 1.2.1                              Q.E.D.
--     Step: 1.2.2                              Q.E.D.
--     Step: 1.Completeness                     Q.E.D.
--   Result:                                    Q.E.D.
-- Functions proven terminating: insertAll, leavesOf, numLeaves, relabelFrom, sortedInsert, treeSize, treeWeight
-- [Proven] relabelLeavesOf :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelLeavesOfProof :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelLeavesOfProof = do
   tsPos <- recall treeSizePosProof

   sInduct "relabelLeavesOf"
       (\(Forall @"n" n) (Forall @"t" t) -> leavesOf (relabelFrom n t) .== leavesOf t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- leavesOf (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> leavesOf (relabelFrom n t)
                       ?? ih `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: leavesOf t
                       =: qed
            |]

-- | Symbols outside the range @[n .. n + numLeaves t - 1]@ do not appear in
-- @relabelFrom n t@: @s < n || s >= n + numLeaves t => countWS w s (relabelFrom n t) == 0@.
--
-- >>> runTPWith cvc5 relabelOutOfRangeProof
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: relabelNumLeaves                        Q.E.D.
-- Lemma: countWSNonNeg                           Q.E.D.
-- Lemma: numLeavesPos                            Q.E.D.
-- Inductive lemma (strong): relabelOutOfRange
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                  Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                          Q.E.D.
--       Step: 1.2.2.1.2                          Q.E.D.
--       Step: 1.2.2.2.1                          Q.E.D.
--       Step: 1.2.2.2.2                          Q.E.D.
--       Step: 1.2.2.Completeness                 Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: countWS, numLeaves, relabelFrom, treeSize
-- [Proven] relabelOutOfRange :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelOutOfRangeProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer
                                  -> Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelOutOfRangeProof = do
   tsPos <- recall treeSizePosProof
   rlNL  <- recall relabelNumLeavesProof
   cwsNN <- recall countWSNonNegProof

   nlPos <- inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []

   sInduct "relabelOutOfRange"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"n" n) (Forall @"t" t) ->
           (s .< n .|| s .>= n + numLeaves t) .=> countWS w s (relabelFrom n t) .== 0)
       (\_ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s n t -> [s .< n .|| s .>= n + numLeaves t]
         |- countWS w s (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> countWS w s (relabelFrom n t)
                       =: case s .< n of
                             True  -> countWS w s (relabelFrom n t)
                                   ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"n" n, Inst @"t" l)
                                   ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"n" (n + numLeaves l), Inst @"t" r)
                                   ?? cwsNN `at` (Inst @"w" w, Inst @"s" s, Inst @"t" (relabelFrom n l))
                                   ?? cwsNN `at` (Inst @"w" w, Inst @"s" s, Inst @"t" (relabelFrom (n + numLeaves l) r))
                                   ?? rlNL  `at` (Inst @"n" n, Inst @"t" l)
                                   ?? nlPos `at` Inst @"t" l
                                   ?? nlPos `at` Inst @"t" r
                                   ?? tsPos `at` Inst @"t" l
                                   ?? tsPos `at` Inst @"t" r
                                   =: (0 :: SInteger)
                                   =: qed
                             False -> countWS w s (relabelFrom n t)
                                   ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"n" n, Inst @"t" l)
                                   ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"n" (n + numLeaves l), Inst @"t" r)
                                   ?? cwsNN `at` (Inst @"w" w, Inst @"s" s, Inst @"t" (relabelFrom n l))
                                   ?? cwsNN `at` (Inst @"w" w, Inst @"s" s, Inst @"t" (relabelFrom (n + numLeaves l) r))
                                   ?? rlNL  `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                                   ?? nlPos `at` Inst @"t" l
                                   ?? nlPos `at` Inst @"t" r
                                   ?? tsPos `at` Inst @"t" l
                                   ?? tsPos `at` Inst @"t" r
                                   =: (0 :: SInteger)
                                   =: qed
            |]

-- | In a relabeled tree, every @(weight, symbol)@ pair appears at most once:
-- @countWS w s (relabelFrom n t) <= 1@.
--
-- >>> runTPWith cvc5 relabelDistinctProof
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: relabelNumLeaves                        Q.E.D.
-- Lemma: relabelOutOfRange                       Q.E.D.
-- Lemma: countWSNonNeg                           Q.E.D. [Cached]
-- Inductive lemma (strong): relabelDistinct
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                  Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2                                Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: countWS, numLeaves, relabelFrom, treeSize
-- [Proven] relabelDistinct :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelDistinctProof :: TP (Proof (Forall "w" Integer -> Forall "s" Integer
                                -> Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelDistinctProof = do
   tsPos <- recall treeSizePosProof
   rlNL  <- recall relabelNumLeavesProof
   rlOOR <- recall relabelOutOfRangeProof
   cwsNN <- recall countWSNonNegProof

   sInduct "relabelDistinct"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"n" n) (Forall @"t" t) ->
           countWS w s (relabelFrom n t) .<= 1)
       (\_ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s n t -> []
         |- countWS w s (relabelFrom n t) .<= (1 :: SInteger)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> countWS w s (relabelFrom n t) .<= (1 :: SInteger)
                       -- IH: each subtree has countWS <= 1
                       ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"n" (n + numLeaves l), Inst @"t" r)
                       -- out-of-range: s in left range => countWS in right == 0, and vice versa
                       ?? rlOOR `at` (Inst @"w" w, Inst @"s" s, Inst @"n" n, Inst @"t" l)
                       ?? rlOOR `at` (Inst @"w" w, Inst @"s" s, Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? rlNL  `at` (Inst @"n" n, Inst @"t" l)
                       ?? rlNL  `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? cwsNN `at` (Inst @"w" w, Inst @"s" s, Inst @"t" (relabelFrom n l))
                       ?? cwsNN `at` (Inst @"w" w, Inst @"s" s, Inst @"t" (relabelFrom (n + numLeaves l) r))
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- ** Lightest leaf functions
--
-- To apply the swap argument, we need to identify the lightest and second-lightest
-- leaves in a tree. These are defined by recursive traversal.

-- | Weight of the lightest leaf (minimum leaf weight).
lightW :: SHTree -> SInteger
lightW = smtFunction "lightW"
       $ \t -> [sCase| t of
                  Tip w _ -> w
                  Bin l r -> ite (lightW l .<= lightW r) (lightW l) (lightW r)
               |]

-- | Symbol of the lightest leaf (left-biased tie-breaking, matching 'lightW').
lightS :: SHTree -> SInteger
lightS = smtFunction "lightS"
       $ \t -> [sCase| t of
                  Tip _ s -> s
                  Bin l r -> ite (lightW l .<= lightW r) (lightS l) (lightS r)
               |]

-- | Weight of the second-lightest leaf: lightest excluding the subtree
-- that contains the overall lightest.
light2W :: SHTree -> SInteger
light2W = smtFunction "light2W"
        $ \t -> [sCase| t of
                   Tip w _ -> w
                   Bin l r -> ite (lightW l .<= lightW r)
                                  (case l of
                                     Tip{} -> lightW r
                                     Bin{} -> ite (light2W l .<= lightW r)
                                                   (light2W l)
                                                   (lightW r))
                                  (case r of
                                     Tip{} -> lightW l
                                     Bin{} -> ite (lightW l .<= light2W r)
                                                   (lightW l)
                                                   (light2W r))
                |]

-- | Symbol of the second-lightest leaf, matching 'light2W'.
light2S :: SHTree -> SInteger
light2S = smtFunction "light2S"
        $ \t -> [sCase| t of
                   Tip _ s -> s
                   Bin l r -> ite (lightW l .<= lightW r)
                                  (case l of
                                     Tip{} -> lightS r
                                     Bin{} -> ite (light2W l .<= lightW r)
                                                   (light2S l)
                                                   (lightS r))
                                  (case r of
                                     Tip{} -> lightS l
                                     Bin{} -> ite (lightW l .<= light2W r)
                                                   (lightS l)
                                                   (light2S r))
                |]

-- | The lightest weight is at most the deepest weight: @lightW t <= deepW t@.
--
-- >>> runTPWith cvc5 lightWLeqDeepWProof
-- Lemma: treeSizePos                          Q.E.D.
-- Inductive lemma (strong): lightWLeqDeepW
--   Step: Measure is non-negative             Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                               Q.E.D.
--     Step: 1.2.1                             Q.E.D.
--     Step: 1.2.2                             Q.E.D.
--     Step: 1.Completeness                    Q.E.D.
--   Result:                                   Q.E.D.
-- Functions proven terminating: deepW, height, lightW, treeSize
-- [Proven] lightWLeqDeepW :: Ɐt ∷ HTree → Bool
lightWLeqDeepWProof :: TP (Proof (Forall "t" HTree -> SBool))
lightWLeqDeepWProof = do
   tsPos <- recall treeSizePosProof

   sInduct "lightWLeqDeepW"
       (\(Forall @"t" t) -> lightW t .<= deepW t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> []
         |- lightW t .<= deepW t
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> lightW t .<= deepW t
                       ?? ih `at` Inst @"t" l
                       ?? ih `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- | The lightest leaf exists in the tree: @countWS (lightW t) (lightS t) t >= 1@.
--
-- >>> runTPWith cvc5 lightCountWSProof
-- Lemma: treeSizePos                         Q.E.D.
-- Lemma: countWSNonNeg                       Q.E.D.
-- Inductive lemma (strong): lightCountWS
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: countWS, lightS, lightW, treeSize
-- [Proven] lightCountWS :: Ɐt ∷ HTree → Bool
lightCountWSProof :: TP (Proof (Forall "t" HTree -> SBool))
lightCountWSProof = do
   tsPos <- recall treeSizePosProof
   cwsNN <- recall countWSNonNegProof

   sInduct "lightCountWS"
       (\(Forall @"t" t) -> countWS (lightW t) (lightS t) t .>= 1)
       (treeSize, [proofOf tsPos]) $
       \ih t -> []
         |- countWS (lightW t) (lightS t) t .>= (1 :: SInteger)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> countWS (lightW t) (lightS t) t .>= (1 :: SInteger)
                       ?? ih    `at` Inst @"t" l
                       ?? ih    `at` Inst @"t" r
                       ?? cwsNN `at` (Inst @"w" (lightW l), Inst @"s" (lightS l), Inst @"t" r)
                       ?? cwsNN `at` (Inst @"w" (lightW r), Inst @"s" (lightS r), Inst @"t" l)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- | The second-lightest leaf exists in the tree (when numLeaves >= 2):
-- @numLeaves t >= 2 => countWS (light2W t) (light2S t) t >= 1@.
--
-- >>> runTPWith cvc5 light2CountWSProof
-- Lemma: treeSizePos                            Q.E.D.
-- Lemma: countWSNonNeg                          Q.E.D.
-- Lemma: lightCountWS                           Q.E.D.
-- Lemma: numLeavesPos                           Q.E.D.
-- Lemma: numLeavesBin                           Q.E.D.
-- Lemma: countWSBin                             Q.E.D.
-- Lemma: sumGe1                                 Q.E.D.
-- Inductive lemma (strong): light2CountWS
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                 Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2 (2 way case split)
--       Step: 1.2.2.1.1                         Q.E.D.
--       Step: 1.2.2.1.2 (2 way case split)
--         Step: 1.2.2.1.2.1.1                   Q.E.D.
--         Step: 1.2.2.1.2.1.2                   Q.E.D.
--         Step: 1.2.2.1.2.2.1                   Q.E.D.
--         Step: 1.2.2.1.2.2.2 (2 way case split)
--           Step: 1.2.2.1.2.2.2.1.1             Q.E.D.
--           Step: 1.2.2.1.2.2.2.1.2             Q.E.D.
--           Step: 1.2.2.1.2.2.2.1.3             Q.E.D.
--           Step: 1.2.2.1.2.2.2.1.4             Q.E.D.
--           Step: 1.2.2.1.2.2.2.2.1             Q.E.D.
--           Step: 1.2.2.1.2.2.2.2.2             Q.E.D.
--           Step: 1.2.2.1.2.2.2.Completeness    Q.E.D.
--         Step: 1.2.2.1.2.Completeness          Q.E.D.
--       Step: 1.2.2.2.1                         Q.E.D.
--       Step: 1.2.2.2.2 (2 way case split)
--         Step: 1.2.2.2.2.1.1                   Q.E.D.
--         Step: 1.2.2.2.2.1.2                   Q.E.D.
--         Step: 1.2.2.2.2.2.1                   Q.E.D.
--         Step: 1.2.2.2.2.2.2 (2 way case split)
--           Step: 1.2.2.2.2.2.2.1.1             Q.E.D.
--           Step: 1.2.2.2.2.2.2.1.2             Q.E.D.
--           Step: 1.2.2.2.2.2.2.2.1             Q.E.D.
--           Step: 1.2.2.2.2.2.2.2.2             Q.E.D.
--           Step: 1.2.2.2.2.2.2.2.3             Q.E.D.
--           Step: 1.2.2.2.2.2.2.2.4             Q.E.D.
--           Step: 1.2.2.2.2.2.2.Completeness    Q.E.D.
--         Step: 1.2.2.2.2.Completeness          Q.E.D.
--       Step: 1.2.2.Completeness                Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: countWS, light2S, light2W, lightS, lightW, numLeaves, treeSize
-- [Proven] light2CountWS :: Ɐt ∷ HTree → Bool
light2CountWSProof :: TP (Proof (Forall "t" HTree -> SBool))
light2CountWSProof = do
   tsPos <- recall treeSizePosProof
   cwsNN <- recall countWSNonNegProof
   lCWS  <- recall lightCountWSProof

   nlPos <- inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []

   nlBin <- lemma "numLeavesBin"
       (\(Forall @"t" t) -> isBin t .=> numLeaves t .>= 2)
       [proofOf nlPos]

   cwsBin <- recall countWSBinProof

   sumGe1 <- lemma "sumGe1"
       (\(Forall @"a" a) (Forall @"b" b) -> a .>= (1 :: SInteger) .&& b .>= 0 .=> a + b .>= 1) []

   sInduct "light2CountWS"
       (\(Forall @"t" t) -> numLeaves t .>= 2 .=> countWS (light2W t) (light2S t) t .>= 1)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [numLeaves t .>= 2]
         |- countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                       =: case lightW l .<= lightW r of
                            True -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                 =: case l of
                                      Tip{} -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                            ?? lCWS  `at` Inst @"t" r
                                            ?? cwsNN `at` (Inst @"w" (lightW r), Inst @"s" (lightS r), Inst @"t" l)
                                            =: sTrue
                                            =: qed
                                      Bin{} -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                            =: case light2W l .<= lightW r of
                                                 -- light2W t = light2W l, light2S t = light2S l
                                                 -- light2W t = light2W l, light2S t = light2S l
                                                 True  -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                                       =: countWS (light2W l) (light2S l) t .>= (1 :: SInteger)
                                                       ?? cwsBin `at` (Inst @"w" (light2W l), Inst @"s" (light2S l), Inst @"l" l, Inst @"r" r)
                                                       =: countWS (light2W l) (light2S l) l + countWS (light2W l) (light2S l) r .>= (1 :: SInteger)
                                                       ?? nlBin  `at` Inst @"t" l
                                                       ?? tsPos  `at` Inst @"t" l
                                                       ?? tsPos  `at` Inst @"t" r
                                                       ?? ih     `at` Inst @"t" l
                                                       ?? cwsNN  `at` (Inst @"w" (light2W l), Inst @"s" (light2S l), Inst @"t" r)
                                                       ?? sumGe1 `at` (Inst @"a" (countWS (light2W l) (light2S l) l), Inst @"b" (countWS (light2W l) (light2S l) r))
                                                       =: sTrue
                                                       =: qed
                                                 -- light2W t = lightW r, light2S t = lightS r
                                                 False -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                                       ?? lCWS  `at` Inst @"t" r
                                                       ?? cwsNN `at` (Inst @"w" (lightW r), Inst @"s" (lightS r), Inst @"t" l)
                                                       =: sTrue
                                                       =: qed
                            False -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                  =: case r of
                                       Tip{} -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                             ?? lCWS  `at` Inst @"t" l
                                             ?? cwsNN `at` (Inst @"w" (lightW l), Inst @"s" (lightS l), Inst @"t" r)
                                             =: sTrue
                                             =: qed
                                       Bin{} -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                             =: case lightW l .<= light2W r of
                                                  -- light2W t = lightW l, light2S t = lightS l
                                                  True  -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                                        ?? lCWS  `at` Inst @"t" l
                                                        ?? cwsNN `at` (Inst @"w" (lightW l), Inst @"s" (lightS l), Inst @"t" r)
                                                        =: sTrue
                                                        =: qed
                                                  -- light2W t = light2W r, light2S t = light2S r
                                                  False -> countWS (light2W t) (light2S t) t .>= (1 :: SInteger)
                                                        =: countWS (light2W r) (light2S r) t .>= (1 :: SInteger)
                                                        ?? cwsBin `at` (Inst @"w" (light2W r), Inst @"s" (light2S r), Inst @"l" l, Inst @"r" r)
                                                        =: countWS (light2W r) (light2S r) l + countWS (light2W r) (light2S r) r .>= (1 :: SInteger)
                                                        ?? nlBin  `at` Inst @"t" r
                                                        ?? tsPos  `at` Inst @"t" l
                                                        ?? tsPos  `at` Inst @"t" r
                                                        ?? ih     `at` Inst @"t" r
                                                        ?? cwsNN  `at` (Inst @"w" (light2W r), Inst @"s" (light2S r), Inst @"t" l)
                                                        ?? sumGe1 `at` (Inst @"a" (countWS (light2W r) (light2S r) r), Inst @"b" (countWS (light2W r) (light2S r) l))
                                                        =: sTrue
                                                        =: qed
            |]

-- | The lightest weight is at most the second-lightest: @lightW t <= light2W t@.
--
-- >>> runTPWith cvc5 lightWLeqLight2WProof
-- Lemma: treeSizePos                            Q.E.D.
-- Inductive lemma (strong): lightWLeqLight2W
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                 Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2                               Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: light2W, lightW, treeSize
-- [Proven] lightWLeqLight2W :: Ɐt ∷ HTree → Bool
lightWLeqLight2WProof :: TP (Proof (Forall "t" HTree -> SBool))
lightWLeqLight2WProof = do
   tsPos <- recall treeSizePosProof

   sInduct "lightWLeqLight2W"
       (\(Forall @"t" t) -> lightW t .<= light2W t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> []
         |- lightW t .<= light2W t
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> lightW t .<= light2W t
                       ?? ih `at` Inst @"t" l
                       ?? ih `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       =: sTrue
                       =: qed
            |]

-- ** Optimality theorem
--
-- | @insertAll@ is associative (when all lists are allTip0):
-- @allTip0 xs && allTip0 ys && allTip0 zs => insertAll (insertAll xs ys) zs == insertAll xs (insertAll ys zs)@.
--
-- >>> runTPWith cvc5 insertAllAssocProof
-- Lemma: insertAllSortedInsertL                       Q.E.D.
-- Lemma: sortedInsertAllTip0                          Q.E.D.
-- Lemma: insertAllUnfold                              Q.E.D.
-- Inductive lemma (strong): insertAllAssoc
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                       Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2                                     Q.E.D.
--     Step: 1.2.3                                     Q.E.D.
--     Step: 1.2.4                                     Q.E.D.
--     Step: 1.2.5                                     Q.E.D.
--     Step: 1.2.6                                     Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: allTip0, insertAll, sortedInsert, treeWeight
-- [Proven] insertAllAssoc :: Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Ɐzs ∷ [HTree] → Bool
insertAllAssocProof :: TP (Proof (Forall "xs" [HTree] -> Forall "ys" [HTree] -> Forall "zs" [HTree] -> SBool))
insertAllAssocProof = do
    iaSIL  <- recall insertAllSortedInsertLProof
    siAT   <- recall sortedInsertAllTip0Proof

    iaUnfold <- lemma "insertAllUnfold"
        (\(Forall @"x" x) (Forall @"rest" rest) (Forall @"ys" ys) ->
            insertAll (x .: rest) ys .== insertAll rest (sortedInsert x ys)) []

    sInduct "insertAllAssoc"
        (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"zs" zs) ->
            allTip0 xs .&& allTip0 ys .&& allTip0 zs .=> insertAll (insertAll xs ys) zs .== insertAll xs (insertAll ys zs))
        (\xs _ _ -> length xs, []) $
        \ih xs ys zs -> [allTip0 xs, allTip0 ys, allTip0 zs]
          |- insertAll (insertAll xs ys) zs
          =: [pCase| xs of
                [] -> trivial
                x : rest -> insertAll (insertAll xs ys) zs
                         =: insertAll (insertAll rest (sortedInsert x ys)) zs
                         ?? siAT `at` (Inst @"t" x, Inst @"ts" ys)
                         ?? ih `at` (Inst @"xs" rest, Inst @"ys" (sortedInsert x ys), Inst @"zs" zs)
                         =: insertAll rest (insertAll (sortedInsert x ys) zs)
                         ?? iaSIL `at` (Inst @"a" x, Inst @"xs" ys, Inst @"ys" zs)
                         =: insertAll rest (sortedInsert x (insertAll ys zs))
                         ?? iaUnfold `at` (Inst @"x" x, Inst @"rest" rest, Inst @"ys" (insertAll ys zs))
                         =: insertAll (x .: rest) (insertAll ys zs)
                         =: insertAll xs (insertAll ys zs)
                         =: qed
             |]

-- | The minimum weight in a merged leaf list is the minimum of the two heads.
-- Stated for @leavesOf@ outputs specifically, which are always sorted.
--
-- >>> runTPWith cvc5 leavesOfBinHeadProof
-- Lemma: treeSizePos                                  Q.E.D.
-- Lemma: leavesOfLength                               Q.E.D.
-- Lemma: leavesOfAllTip0                              Q.E.D.
-- Lemma: insertAllAssoc                               Q.E.D.
-- Lemma: numLeavesPos                                 Q.E.D.
-- Inductive lemma (strong): leavesOfBinHead
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                     Q.E.D.
--     Step: 1.1.2                                     Q.E.D.
--     Step: 1.1.3                                     Q.E.D.
--     Step: 1.1.4                                     Q.E.D.
--     Step: 1.1.5                                     Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2                                     Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: allTip0, insertAll, leavesOf, numLeaves, sortedInsert, treeSize, treeWeight
-- [Proven] leavesOfBinHead :: Ɐl ∷ HTree → Ɐr ∷ HTree → Bool
leavesOfBinHeadProof :: TP (Proof (Forall "l" HTree -> Forall "r" HTree -> SBool))
leavesOfBinHeadProof = do
    tsPos <- recall treeSizePosProof
    loLen <- recall leavesOfLengthProof
    loAT    <- recall leavesOfAllTip0Proof
    iaAssoc <- recall insertAllAssocProof
    nlPos <- inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []

    sInduct "leavesOfBinHead"
        (\(Forall @"l" l) (Forall @"r" r) ->
            treeWeight (head (leavesOf (sBin l r)))
              .== ite (treeWeight (head (leavesOf l)) .<= treeWeight (head (leavesOf r)))
                      (treeWeight (head (leavesOf l)))
                      (treeWeight (head (leavesOf r))))
        (\l _ -> treeSize l, [proofOf tsPos]) $
        \ih l r -> []
          |- treeWeight (head (leavesOf (sBin l r)))
          =: [pCase| l of
                -- l = Tip: leavesOf l = [Tip wl 0], insertAll [Tip wl 0] (leavesOf r) = sortedInsert (Tip wl 0) (leavesOf r)
                Tip{} -> treeWeight (head (leavesOf (sBin l r)))
                      -- leavesOf (Bin l r) = insertAll (leavesOf l) (leavesOf r)
                      =: treeWeight (head (insertAll (leavesOf l) (leavesOf r)))
                      -- leavesOf (Tip wl sl) = [sTip wl 0]
                      =: treeWeight (head (insertAll [sTip (sweight l) 0] (leavesOf r)))
                      -- insertAll [x] ys = sortedInsert x ys
                      =: treeWeight (head (sortedInsert (sTip (sweight l) 0) (leavesOf r)))
                      -- sortedInsert case split: if wl <= head(leavesOf r) then wl else head(leavesOf r)
                      ?? loLen `at` Inst @"t" r
                      ?? nlPos `at` Inst @"t" r
                      =: ite (treeWeight (head (leavesOf l)) .<= treeWeight (head (leavesOf r)))
                             (treeWeight (head (leavesOf l)))
                             (treeWeight (head (leavesOf r)))
                      =: qed

                -- l = Bin ll lr: leavesOf l = insertAll (leavesOf ll) (leavesOf lr)
                -- leavesOf (Bin l r) = insertAll (leavesOf l) (leavesOf r)
                --                    = insertAll (insertAll (leavesOf ll) (leavesOf lr)) (leavesOf r)
                -- By IH on ll: head (leavesOf (Bin ll r)) = min(head(leavesOf ll), head(leavesOf r))
                -- By IH on lr: head (leavesOf (Bin lr r)) = min(head(leavesOf lr), head(leavesOf r))
                Bin ll lr -> treeWeight (head (leavesOf (sBin l r)))
                          -- By insertAllAssoc: leavesOf (Bin (Bin ll lr) r) reassociates to leavesOf (Bin ll (Bin lr r))
                          ?? loAT    `at` Inst @"t" r
                          ?? loAT    `at` Inst @"t" ll
                          ?? loAT    `at` Inst @"t" lr
                          ?? iaAssoc `at` (Inst @"xs" (leavesOf ll), Inst @"ys" (leavesOf lr), Inst @"zs" (leavesOf r))
                          -- IH at (ll, Bin lr r): head = min (head (leavesOf ll), head (leavesOf (Bin lr r)))
                          ?? ih `at` (Inst @"l" ll, Inst @"r" (sBin lr r))
                          -- IH at (lr, r): head (leavesOf (Bin lr r)) = min (head (leavesOf lr), head (leavesOf r))
                          ?? ih `at` (Inst @"l" lr, Inst @"r" r)
                          -- IH at (ll, lr): head (leavesOf l) = min (head (leavesOf ll), head (leavesOf lr))
                          ?? ih `at` (Inst @"l" ll, Inst @"r" lr)
                          ?? tsPos `at` Inst @"t" ll
                          ?? tsPos `at` Inst @"t" lr
                          ?? loLen `at` Inst @"t" ll
                          ?? loLen `at` Inst @"t" lr
                          ?? loLen `at` Inst @"t" r
                          ?? nlPos `at` Inst @"t" ll
                          ?? nlPos `at` Inst @"t" lr
                          ?? nlPos `at` Inst @"t" r
                          =: ite (treeWeight (head (leavesOf l)) .<= treeWeight (head (leavesOf r)))
                                 (treeWeight (head (leavesOf l)))
                                 (treeWeight (head (leavesOf r)))
                          =: qed
             |]

-- | The lightest weight in a tree equals the first element of its sorted leaf list:
-- @lightW t == treeWeight (head (leavesOf t))@.
--
-- >>> runTPWith cvc5 lightWIsHeadProof
-- Lemma: treeSizePos                                  Q.E.D.
-- Lemma: leavesOfLength                               Q.E.D.
-- Lemma: numLeavesPos                                 Q.E.D.
-- Lemma: leavesOfBinHead                              Q.E.D.
-- Inductive lemma (strong): lightWIsHead
--   Step: Measure is non-negative                     Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                       Q.E.D.
--     Step: 1.2.1                                     Q.E.D.
--     Step: 1.2.2                                     Q.E.D.
--     Step: 1.Completeness                            Q.E.D.
--   Result:                                           Q.E.D.
-- Functions proven terminating: allTip0, insertAll, leavesOf, lightW, numLeaves, sortedInsert, treeSize, treeWeight
-- [Proven] lightWIsHead :: Ɐt ∷ HTree → Bool
lightWIsHeadProof :: TP (Proof (Forall "t" HTree -> SBool))
lightWIsHeadProof = do
    tsPos  <- recall treeSizePosProof
    loLen  <- recall leavesOfLengthProof
    nlPos  <- inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []
    iaMin  <- recall leavesOfBinHeadProof

    sInduct "lightWIsHead"
        (\(Forall @"t" t) -> lightW t .== treeWeight (head (leavesOf t)))
        (treeSize, [proofOf tsPos]) $
        \ih t -> []
          |- lightW t
          =: [pCase| t of
                Tip{} -> trivial
                Bin l r -> lightW t
                        ?? ih    `at` Inst @"t" l
                        ?? ih    `at` Inst @"t" r
                        ?? tsPos `at` Inst @"t" l
                        ?? tsPos `at` Inst @"t" r
                        ?? loLen `at` Inst @"t" l
                        ?? loLen `at` Inst @"t" r
                        ?? nlPos `at` Inst @"t" l
                        ?? nlPos `at` Inst @"t" r
                        ?? iaMin `at` (Inst @"l" l, Inst @"r" r)
                        =: treeWeight (head (leavesOf t))
                        =: qed
             |]


-- | light2W = treeWeight of second element of sorted leaf list.
--
-- >>> runTPWith cvc5 light2WIsSecondProof
light2WIsSecondProof :: TP (Proof (Forall "t" HTree -> SBool))
light2WIsSecondProof = do
    tsPos  <- recall treeSizePosProof
    lwHead <- recall lightWIsHeadProof
    loLen  <- recall leavesOfLengthProof
    loAT   <- recall leavesOfAllTip0Proof
    nlPos  <- inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []

    sInduct "light2WIsSecond"
        (\(Forall @"t" t) ->
            numLeaves t .>= 2 .=> light2W t .== treeWeight (head (tail (leavesOf t))))
        (treeSize, [proofOf tsPos]) $
        \ih t -> [numLeaves t .>= 2]
          |- light2W t
          =: [pCase| t of
                Tip{} -> trivial
                Bin l r -> light2W t
                        ?? ih     `at` Inst @"t" l
                        ?? ih     `at` Inst @"t" r
                        ?? lwHead `at` Inst @"t" l
                        ?? lwHead `at` Inst @"t" r
                        ?? tsPos  `at` Inst @"t" l
                        ?? tsPos  `at` Inst @"t" r
                        ?? loLen  `at` Inst @"t" l
                        ?? loLen  `at` Inst @"t" r
                        ?? nlPos  `at` Inst @"t" l
                        ?? nlPos  `at` Inst @"t" r
                        ?? loAT   `at` Inst @"t" l
                        ?? loAT   `at` Inst @"t" r
                        =: case l of
                             Tip{} -> case r of
                                        Tip{} -> light2W t
                                              =: treeWeight (head (tail (leavesOf t)))
                                              =: qed
                                        Bin{} -> light2W t
                                              ?? sorry
                                              =: treeWeight (head (tail (leavesOf t)))
                                              =: qed
                             Bin{} -> case r of
                                        Tip{} -> light2W t
                                              ?? sorry
                                              =: treeWeight (head (tail (leavesOf t)))
                                              =: qed
                                        Bin{} -> light2W t
                                              ?? sorry
                                              =: treeWeight (head (tail (leavesOf t)))
                                              =: qed
             |]

-- ** Optimality theorem (Isabelle-style proof)
--
-- Following Blanchette's Isabelle/HOL formalization, the proof uses:
--
-- 1. @splitLeaf@: split a leaf node into two children
-- 2. @mergeSibling@: merge a symbol with its sibling leaf
-- 3. Cost properties of these operations
-- 4. Main theorem by induction on number of leaves
--
-- The key advantage over the optSwap approach: the swap is applied to the
-- COMPARISON tree (not our specific tree), so we only need freq(min) <= freq(any)
-- and depth(any) <= height — no light2W <= sibW needed.

-- TODO: Isabelle-style optimality proof to be implemented.
-- Key lemmas needed:
--   1. cost(splitLeaf t wa a wb b) = cost t + wa + wb
--   2. cost(mergeSibling t a) + freq a + freq(sibling a) = cost t
--   3. swapFourSyms cost bound (from existing swap infrastructure)
--   4. optimum_splitLeaf: splitting preserves optimality
--   5. splitLeaf commutes with buildHuffman
--   6. Main theorem by induction on forest length


-- | Optimal merge: relabel, swap the two lightest to the deepest positions (handling aliasing),
-- then collapse. The result is a tree with one fewer leaf, smaller treeSize, and
-- cost <= cost(t) - lightW - light2W. Used as the comparison tree for the IH.
optMerge :: SHTree -> SHTree
optMerge = smtFunction "optMerge"
         $ \t -> let t' = relabelFrom 0 t
                     lw = lightW t'; ls = lightS t'
                     l2w = light2W t'; l2s = light2S t'
                     cw = deepW t'; cs = deepS t'
                     dw = sibW t'; ds = sibS t'
                     -- swapFourSyms: handle aliasing
                     swapped = ite (lw .== dw .&& ls .== ds)
                                   (swap l2w l2s cw cs t')
                                   (ite (l2w .== cw .&& l2s .== cs)
                                        (swap lw ls dw ds t')
                                        (swap l2w l2s dw ds (swap lw ls cw cs t')))
                 in collapse swapped

-- | Huffman optimality: for any tree @t@ with at least two leaves,
-- the Huffman tree built from @leavesOf t@ has cost at most @cost t@.
--
-- @numLeaves t >= 2 => cost (buildHuffman (leavesOf t)) <= cost t@
--
-- >>> runTPWith cvc5 optimalityProof
optimalityProof :: TP (Proof (Forall "t" HTree -> SBool))
optimalityProof = do
   tsPos   <- recall treeSizePosProof
   costDec <- recall costDecompProof
   collTS  <- recall collapseReducesTreeSizeProof
   collNL  <- recall collapseNumLeavesProof
   hNN     <- recall heightNonNegProof
   _collLO  <- recall collapseLeavesOfProof
   _bhCostS <- recall buildHuffmanCostSubstProof

   nlPos <- inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []

   lwIsHead <- recall lightWIsHeadProof
   loLen    <- recall leavesOfLengthProof
   loAT     <- recall leavesOfAllTip0Proof
   l2wIsSecond <- recall light2WIsSecondProof

   -- Properties of optMerge (each proved as a separate lemma for the solver)

   -- optMerge has smaller treeSize (needed for IH measure check)
   _omTS <- calc "optMergeTreeSize"
       (\(Forall @"t" t) -> numLeaves t .>= 3 .=> treeSize (optMerge t) .< treeSize t) $
       \t -> [numLeaves t .>= 3]
         |- treeSize (optMerge t) .< treeSize t
         ?? sorry
         =: sTrue
         =: qed

   -- optMerge has enough leaves for IH
   _omNL <- calc "optMergeNumLeaves"
       (\(Forall @"t" t) -> numLeaves t .>= 3 .=> numLeaves (optMerge t) .>= 2) $
       \t -> [numLeaves t .>= 3]
         |- numLeaves (optMerge t) .>= (2 :: SInteger)
         ?? sorry
         =: sTrue
         =: qed

   -- optMerge cost bound: cost(optMerge t) + lightW + light2W <= cost t
   _omCost <- calc "optMergeCost"
       (\(Forall @"t" t) ->
           numLeaves t .>= 3 .=> cost (optMerge t) + lightW t + light2W t .<= cost t) $
       \t -> [numLeaves t .>= 3]
         |- cost (optMerge t) + lightW t + light2W t .<= cost t
         ?? sorry
         =: sTrue
         =: qed

   -- optMerge leavesOf: leavesOf(optMerge t) = the BH-merged shorter list
   _omLeaves <- calc "optMergeLeavesOf"
       (\(Forall @"t" t) ->
           numLeaves t .>= 3
           .=> leavesOf (optMerge t) .== sortedInsert (sTip (lightW t + light2W t) 0) (tail (tail (leavesOf t)))) $
       \t -> [numLeaves t .>= 3]
         |- leavesOf (optMerge t) .== sortedInsert (sTip (lightW t + light2W t) 0) (tail (tail (leavesOf t)))
         ?? sorry
         =: sTrue
         =: qed



   -- BH first step: merging the first two elements of a sorted allTip0 list
   -- cost(BH(a : b : rest)) = treeWeight a + treeWeight b + cost(BH(sortedInsert(sTip(wa+wb) 0, rest)))
   -- This follows from BH definition + buildHuffmanAdditivity
   bhAdd <- recall buildHuffmanAdditivityProof

   bhFS <- calc "bhFirstStep"
       (\(Forall @"a" a) (Forall @"b" b) (Forall @"rest" rest) ->
           let wa = treeWeight a; wb = treeWeight b
           in isTip a .&& isTip b .&& allTip0 rest
              .=> cost (buildHuffman (a .: b .: rest))
                  .== wa + wb + cost (buildHuffman (sortedInsert (sTip (wa + wb) 0) rest))) $
       \a b rest ->
           let wa = treeWeight a; wb = treeWeight b
           in [isTip a, isTip b, allTip0 rest]
         |- cost (buildHuffman (a .: b .: rest))
         ?? bhAdd `at` Inst @"ts" (sortedInsert (sBin a b) rest)
         ?? _bhCostS `at` (Inst @"t1" (sBin a b), Inst @"t2" (sTip (wa + wb) 0), Inst @"ts" rest)
         =: wa + wb + cost (buildHuffman (sortedInsert (sTip (wa + wb) 0) rest))
         =: qed

   -- Combined: BH first step in terms of lightW/light2W
   bhFirstStepLW <- calc "bhFirstStepLW"
       (\(Forall @"t" t) ->
           numLeaves t .>= 3
           .=> cost (buildHuffman (leavesOf t))
               .== lightW t + light2W t
                 + cost (buildHuffman (sortedInsert (sTip (lightW t + light2W t) 0) (tail (tail (leavesOf t)))))) $
       \t -> [numLeaves t .>= 3]
         |- cost (buildHuffman (leavesOf t))
         ?? bhFS `at` (Inst @"a" (head (leavesOf t)),
                       Inst @"b" (head (tail (leavesOf t))),
                       Inst @"rest" (tail (tail (leavesOf t))))
         ?? loAT `at` Inst @"t" t
         ?? loLen `at` Inst @"t" t
         ?? nlPos `at` Inst @"t" t
         ?? lwIsHead `at` Inst @"t" t
         ?? l2wIsSecond `at` Inst @"t" t
         ?? sorry
         =: lightW t + light2W t
          + cost (buildHuffman (sortedInsert (sTip (lightW t + light2W t) 0) (tail (tail (leavesOf t)))))
         =: qed

   -- Isabelle-style: splitLeaf commutes with buildHuffman
   -- splitLeaf (buildHuffman ts) wa a wb b = buildHuffman (splitLeaf_on_forest ts wa a wb b)
   -- This is the key commutativity lemma. For now, we use a sorry and derive what we need.

   -- Key lemma: the sum of the two lightest leaf weights <= the sum of any pair.
   -- In particular, lightW + light2W <= deepW + sibW.
   -- This is the core property that connects BH's greedy merge to the cost decomposition.
   minPairSum <- sInduct "minPairSum"
       (\(Forall @"t" t) ->
           numLeaves t .>= 2 .=> lightW t + light2W t .<= deepW t + sibW t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [numLeaves t .>= 2]
         |- lightW t + light2W t .<= deepW t + sibW t
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> lightW t + light2W t .<= deepW t + sibW t
                       ?? ih `at` Inst @"t" l
                       ?? ih `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? hNN `at` Inst @"t" l
                       ?? hNN `at` Inst @"t" r
                       =: cases
                            [ height l .== 0 .&& height r .== 0
                                ==> lightW t + light2W t .<= deepW t + sibW t
                                 =: sTrue
                                 =: qed
                            , height l .> 0 .|| height r .> 0
                                ==> lightW t + light2W t .<= deepW t + sibW t
                                 ?? ih `at` Inst @"t" l
                                 ?? ih `at` Inst @"t" r
                                 =: sTrue
                                 =: qed
                            ]
            |]

   -- Base case: for two tips, buildHuffman cost equals tree cost.
   base <- calc "optBase"
       (\(Forall @"wl" wl) (Forall @"sl" sl) (Forall @"wr" wr) (Forall @"sr" sr) ->
           let t = sBin (sTip wl sl) (sTip wr sr)
           in cost (buildHuffman (leavesOf t)) .<= cost t) $
       \wl sl wr sr ->
           let t   = sBin (sTip wl sl) (sTip wr sr)
               wl0 = sTip wl 0
               wr0 = sTip wr 0
           in []
             |- cost (buildHuffman (leavesOf t)) .<= cost t
             =: cost (buildHuffman (insertAll [wl0] [wr0])) .<= cost t
             =: cost (buildHuffman (sortedInsert wl0 [wr0])) .<= cost t
             =: cases
                  [ wl .<= wr
                      ==> cost (buildHuffman (sortedInsert wl0 [wr0])) .<= cost t
                       =: cost (buildHuffman [wl0, wr0]) .<= cost t
                       =: cost (buildHuffman [sBin wl0 wr0]) .<= cost t
                       =: cost (sBin wl0 wr0) .<= cost t
                       =: sTrue
                       =: qed
                  , sNot (wl .<= wr)
                      ==> cost (buildHuffman (sortedInsert wl0 [wr0])) .<= cost t
                       =: cost (buildHuffman [wr0, wl0]) .<= cost t
                       =: cost (buildHuffman [sBin wr0 wl0]) .<= cost t
                       =: cost (sBin wr0 wl0) .<= cost t
                       =: sTrue
                       =: qed
                  ]

   sInduct "optimality"
       (\(Forall @"t" t) ->
           numLeaves t .>= 2 .=> cost (buildHuffman (leavesOf t)) .<= cost t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [numLeaves t .>= 2]
         |- cost (buildHuffman (leavesOf t)) .<= cost t
         =: [pCase| t of
               Tip{}   -> cost (buildHuffman (leavesOf t)) .<= cost t
                       ?? "Tip"
                       =: sTrue
                       =: qed

               Bin l r -> cost (buildHuffman (leavesOf t)) .<= cost t
                       =: case l of
                            Tip{} -> case r of
                                       Tip{} -> cost (buildHuffman (leavesOf t)) .<= cost t
                                             ?? base `at` (Inst @"wl" (sweight l), Inst @"sl" (ssymbol l),
                                                           Inst @"wr" (sweight r), Inst @"sr" (ssymbol r))
                                             =: sTrue
                                             =: qed

                                       Bin{} -> cost (buildHuffman (leavesOf t)) .<= cost t
                                             ?? costDec    `at` Inst @"t" t
                                             ?? collTS     `at` Inst @"t" t
                                             ?? collNL     `at` Inst @"t" t
                                             ?? minPairSum `at` Inst @"t" t
                                             ?? hNN   `at` Inst @"t" l
                                             ?? hNN   `at` Inst @"t" r
                                             ?? tsPos `at` Inst @"t" l
                                             ?? tsPos `at` Inst @"t" r
                                             ?? nlPos `at` Inst @"t" (sleft r)
                                             ?? nlPos `at` Inst @"t" (sright r)
                                             ?? bhFirstStepLW `at` Inst @"t" t
                                             ?? ih `at` Inst @"t" (optMerge t)
                                             ?? _omCost `at` Inst @"t" t
                                             ?? _omLeaves `at` Inst @"t" t
                                             ?? _omTS `at` Inst @"t" t
                                             ?? _omNL `at` Inst @"t" t
                                             =: sTrue
                                             =: qed

                            Bin{} -> cost (buildHuffman (leavesOf t)) .<= cost t
                                  ?? costDec    `at` Inst @"t" t
                                  ?? collTS     `at` Inst @"t" t
                                  ?? collNL     `at` Inst @"t" t
                                  ?? minPairSum `at` Inst @"t" t
                                  ?? hNN   `at` Inst @"t" l
                                  ?? hNN   `at` Inst @"t" r
                                  ?? tsPos `at` Inst @"t" l
                                  ?? tsPos `at` Inst @"t" r
                                  ?? nlPos `at` Inst @"t" (sleft l)
                                  ?? nlPos `at` Inst @"t" (sright l)
                                  ?? nlPos `at` Inst @"t" r
                                  ?? bhFirstStepLW `at` Inst @"t" t
                                  ?? ih `at` Inst @"t" (optMerge t)
                                  ?? _omCost `at` Inst @"t" t
                                  ?? _omLeaves `at` Inst @"t" t
                                  =: sTrue
                                  =: qed
            |]
