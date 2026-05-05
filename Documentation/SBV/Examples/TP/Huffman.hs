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

-- | Tree size is always at least 1.
--
-- >>> runTPWith cvc5 treeSizePos
-- Inductive lemma: treeSizePos                  Q.E.D.
-- Functions proven terminating: treeSize
-- [Proven] treeSizePos :: Ɐt ∷ HTree → Bool
treeSizePos :: TP (Proof (Forall "t" HTree -> SBool))
treeSizePos = inductiveLemma "treeSizePos" (\(Forall @"t" t) -> treeSize t .>= 1) []

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
findPath :: SInteger -> SHTree -> SList Bool
findPath = smtFunction "findPath"
         $ \s t -> [sCase| t of
                      Tip{}   -> []
                      Bin l r | member s l -> sFalse .: findPath s l
                              | True       -> sTrue  .: findPath s r
                   |]

-- | Decode a bit path through a tree, returning the symbol at the destination leaf.
decode :: SList Bool -> SHTree -> SInteger
decode = smtFunction "decode"
       $ \bs t -> [sCase| t of
                     Tip _ x -> x
                     Bin l r -> case bs of
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
   tsPos <- recall treeSizePos

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
--
-- Each function is defined with its body factored out, followed by an unfolding
-- lemma that the solver can verify trivially. These lemmas are later recalled
-- as hints when the solver needs to see through a function definition.

-- ** Tree metrics

-- | Body of 'treeWeight'.
treeWeightBody :: SHTree -> SInteger
treeWeightBody t = [sCase| t of
                      Tip w _ -> w
                      Bin l r -> treeWeight l + treeWeight r
                   |]

-- | Total weight of a tree: sum of all leaf weights.
treeWeight :: SHTree -> SInteger
treeWeight = smtFunction "treeWeight" treeWeightBody

-- | Unfolding lemma for 'treeWeight'.
--
-- >>> runTPWith cvc5 treeWeightUnfold
-- Lemma: treeWeightUnfold                       Q.E.D.
-- Functions proven terminating: treeWeight
-- [Proven] treeWeightUnfold :: Ɐt ∷ HTree → Bool
treeWeightUnfold :: TP (Proof (Forall "t" HTree -> SBool))
treeWeightUnfold = lemma "treeWeightUnfold" (\(Forall @"t" t) -> treeWeight t .== treeWeightBody t) []

-- | Body of 'cost'.
costBody :: SHTree -> SInteger
costBody t = [sCase| t of
                Tip{}   -> 0
                Bin l r -> cost l + cost r + treeWeight l + treeWeight r
             |]

-- | Cost of a tree (weighted path length): merging two subtrees adds their combined weight.
cost :: SHTree -> SInteger
cost = smtFunction "cost" costBody

-- | Unfolding lemma for 'cost'.
--
-- >>> runTPWith cvc5 costUnfold
-- Lemma: costUnfold                             Q.E.D.
-- Functions proven terminating: cost, treeWeight
-- [Proven] costUnfold :: Ɐt ∷ HTree → Bool
costUnfold :: TP (Proof (Forall "t" HTree -> SBool))
costUnfold = lemma "costUnfold" (\(Forall @"t" t) -> cost t .== costBody t) []

-- | Body of 'numLeaves'.
numLeavesBody :: SHTree -> SInteger
numLeavesBody t = [sCase| t of
                     Tip{}   -> 1
                     Bin l r -> numLeaves l + numLeaves r
                  |]

-- | Number of leaves in a tree.
numLeaves :: SHTree -> SInteger
numLeaves = smtFunction "numLeaves" numLeavesBody

-- | Unfolding lemma for 'numLeaves'.
--
-- >>> runTPWith cvc5 numLeavesUnfold
-- Lemma: numLeavesUnfold                        Q.E.D.
-- Functions proven terminating: numLeaves
-- [Proven] numLeavesUnfold :: Ɐt ∷ HTree → Bool
numLeavesUnfold :: TP (Proof (Forall "t" HTree -> SBool))
numLeavesUnfold = lemma "numLeavesUnfold" (\(Forall @"t" t) -> numLeaves t .== numLeavesBody t) []

-- | Body of 'height'.
heightBody :: SHTree -> SInteger
heightBody t = [sCase| t of
                  Tip{}   -> 0
                  Bin l r -> 1 + smax (height l) (height r)
               |]

-- | Height of a tree.
height :: SHTree -> SInteger
height = smtFunction "height" heightBody

-- | Unfolding lemma for 'height'.
--
-- >>> runTPWith cvc5 heightUnfold
-- Lemma: heightUnfold                           Q.E.D.
-- [Proven] heightUnfold :: Ɐt ∷ HTree → Bool
heightUnfold :: TP (Proof (Forall "t" HTree -> SBool))
heightUnfold = lemma "heightUnfold" (\(Forall @"t" t) -> height t .== heightBody t) []

-- | Body of 'countWS'.
countWSBody :: SInteger -> SInteger -> SHTree -> SInteger
countWSBody w s t = [sCase| t of
                       Tip tw ts -> ite (w .== tw .&& s .== ts) 1 0
                       Bin l r   -> countWS w s l + countWS w s r
                    |]

-- | Count leaves matching a specific (weight, symbol) pair.
countWS :: SInteger -> SInteger -> SHTree -> SInteger
countWS = smtFunction "countWS" countWSBody

-- | Unfolding lemma for 'countWS'.
--
-- >>> runTPWith cvc5 countWSUnfold
-- Lemma: countWSUnfold                          Q.E.D.
-- [Proven] countWSUnfold :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
countWSUnfold :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
countWSUnfold = lemma "countWSUnfold"
    (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) -> countWS w s t .== countWSBody w s t) []

-- ** Swap

-- | Body of 'swap'.
swapBody :: SInteger -> SInteger -> SInteger -> SInteger -> SHTree -> SHTree
swapBody wa sa wb sb t =
    [sCase| t of
       Tip w s | s .== sa .&& w .== wa -> sTip wb sb
               | s .== sb .&& w .== wb -> sTip wa sa
               | True                  -> sTip w s
       Bin l r -> sBin (swap wa sa wb sb l) (swap wa sa wb sb r)
    |]

-- | Swap two symbols (and their weights) in a tree.
swap :: SInteger -> SInteger -> SInteger -> SInteger -> SHTree -> SHTree
swap = smtFunction "swap" swapBody

-- | Unfolding lemma for 'swap'.
--
-- >>> runTPWith cvc5 swapUnfold
-- Lemma: swapUnfold                             Q.E.D.
-- [Proven] swapUnfold :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapUnfold :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapUnfold = lemma "swapUnfold"
    (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) -> swap wa sa wb sb t .== swapBody wa sa wb sb t) []

-- ** Collapse

-- | Body of 'collapse'.
collapseBody :: SHTree -> SHTree
collapseBody t = [sCase| t of
                    Tip w s -> sTip w s
                    Bin l r | height l .>= height r .&& height l .== 0 -> sTip (treeWeight l + treeWeight r) 0
                            | height l .>= height r                    -> sBin (collapse l) r
                            | height r .== 0                           -> sTip (treeWeight l + treeWeight r) 0
                            | True                                     -> sBin l (collapse r)
                 |]

-- | Collapse: merge the deepest pair of siblings into a single leaf.
collapse :: SHTree -> SHTree
collapse = smtFunction "collapse" collapseBody

-- | Unfolding lemma for 'collapse'.
--
-- >>> runTPWith cvc5 collapseUnfold
-- Lemma: collapseUnfold                         Q.E.D.
-- [Proven] collapseUnfold :: Ɐt ∷ HTree → Bool
collapseUnfold :: TP (Proof (Forall "t" HTree -> SBool))
collapseUnfold = lemma "collapseUnfold"
    (\(Forall @"t" t) -> collapse t .== collapseBody t) []

-- ** Sorted forests and Huffman construction

-- | Body of 'sortedInsert'.
sortedInsertBody :: SHTree -> SList HTree -> SList HTree
sortedInsertBody t ts = [sCase| ts of
                           []                                     -> [t]
                           u : us | treeWeight t .<= treeWeight u -> t .: u .: us
                                  | True                          -> u .: sortedInsert t us
                        |]

-- | Insert a tree into a weight-sorted forest, maintaining sort order.
sortedInsert :: SHTree -> SList HTree -> SList HTree
sortedInsert = smtFunction "sortedInsert" sortedInsertBody

-- | Unfolding lemma for 'sortedInsert'.
--
-- >>> runTPWith cvc5 sortedInsertUnfold
-- Lemma: sortedInsertUnfold                     Q.E.D.
-- [Proven] sortedInsertUnfold :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertUnfold :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertUnfold = lemma "sortedInsertUnfold"
    (\(Forall @"t" t) (Forall @"ts" ts) -> sortedInsert t ts .== sortedInsertBody t ts) []

-- | Sorted insertion preserves length (needed as a measure helper for 'buildHuffman').
--
-- >>> runTPWith cvc5 sortedInsertLength
-- Inductive lemma (strong): sortedInsertLength
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                 Q.E.D.
--     Step: 1.2 (2 way case split)
--       Step: 1.2.1.1                           Q.E.D.
--       Step: 1.2.2.1                           Q.E.D.
--       Step: 1.2.Completeness                  Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- [Proven] sortedInsertLength :: Ɐt ∷ HTree → Ɐts ∷ [HTree] → Bool
sortedInsertLength :: TP (Proof (Forall "t" HTree -> Forall "ts" [HTree] -> SBool))
sortedInsertLength =
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

-- | Body of 'insertAll'.
insertAllBody :: SList HTree -> SList HTree -> SList HTree
insertAllBody xs ys = [sCase| xs of
                         []       -> ys
                         x : rest -> insertAll rest (sortedInsert x ys)
                      |]

-- | Insert all elements of one forest into another, maintaining sort order.
insertAll :: SList HTree -> SList HTree -> SList HTree
insertAll = smtFunction "insertAll" insertAllBody

-- | Unfolding lemma for 'insertAll'.
--
-- >>> runTPWith cvc5 insertAllUnfold
-- Lemma: insertAllUnfold                        Q.E.D.
-- [Proven] insertAllUnfold :: Ɐxs ∷ [HTree] → Ɐys ∷ [HTree] → Bool
insertAllUnfold :: TP (Proof (Forall "xs" [HTree] -> Forall "ys" [HTree] -> SBool))
insertAllUnfold = lemma "insertAllUnfold"
    (\(Forall @"xs" xs) (Forall @"ys" ys) -> insertAll xs ys .== insertAllBody xs ys) []

-- | Body of 'leavesOf'.
leavesOfBody :: SHTree -> SList HTree
leavesOfBody t = [sCase| t of
                    Tip w _ -> [sTip w 0]
                    Bin l r -> insertAll (leavesOf l) (leavesOf r)
                 |]

-- | Extract a sorted, weight-only leaf list from a tree.
leavesOf :: SHTree -> SList HTree
leavesOf = smtFunction "leavesOf" leavesOfBody

-- | Unfolding lemma for 'leavesOf'.
--
-- >>> runTPWith cvc5 leavesOfUnfold
-- Lemma: leavesOfUnfold                         Q.E.D.
-- [Proven] leavesOfUnfold :: Ɐt ∷ HTree → Bool
leavesOfUnfold :: TP (Proof (Forall "t" HTree -> SBool))
leavesOfUnfold = lemma "leavesOfUnfold"
    (\(Forall @"t" t) -> leavesOf t .== leavesOfBody t) []

-- | Body of 'buildHuffman'.
buildHuffmanBody :: SList HTree -> SHTree
buildHuffmanBody ts = [sCase| ts of
                         []     -> sTip 0 0
                         t : rest -> case rest of
                                       []     -> t
                                       u : us -> buildHuffman (sortedInsert (sBin t u) us)
                      |]

-- | Build the Huffman tree from a weight-sorted list of leaves.
buildHuffman :: SList HTree -> SHTree
buildHuffman = smtFunctionWithMeasure "buildHuffman"
                 (length @HTree, [measureLemma sortedInsertLength])
                 buildHuffmanBody

-- | Unfolding lemma for 'buildHuffman'.
--
-- >>> runTPWith cvc5 buildHuffmanUnfold
-- Lemma: buildHuffmanUnfold                     Q.E.D.
-- [Proven] buildHuffmanUnfold :: Ɐts ∷ [HTree] → Bool
buildHuffmanUnfold :: TP (Proof (Forall "ts" [HTree] -> SBool))
buildHuffmanUnfold = lemma "buildHuffmanUnfold"
    (\(Forall @"ts" ts) -> buildHuffman ts .== buildHuffmanBody ts) []

-- ** Lightest and deepest leaf accessors

-- | Body of 'lightW'.
lightWBody :: SHTree -> SInteger
lightWBody t = [sCase| t of
                  Tip w _ -> w
                  Bin l r -> smin (lightW l) (lightW r)
               |]

-- | Weight of the lightest leaf.
lightW :: SHTree -> SInteger
lightW = smtFunction "lightW" lightWBody

-- | Unfolding lemma for 'lightW'.
--
-- >>> runTPWith cvc5 lightWUnfold
-- Lemma: lightWUnfold                           Q.E.D.
-- [Proven] lightWUnfold :: Ɐt ∷ HTree → Bool
lightWUnfold :: TP (Proof (Forall "t" HTree -> SBool))
lightWUnfold = lemma "lightWUnfold"
    (\(Forall @"t" t) -> lightW t .== lightWBody t) []

-- | Body of 'lightS'.
lightSBody :: SHTree -> SInteger
lightSBody t = [sCase| t of
                  Tip _ s -> s
                  Bin l r | lightW l .<= lightW r -> lightS l
                          | True                  -> lightS r
               |]

-- | Symbol of the lightest leaf.
lightS :: SHTree -> SInteger
lightS = smtFunction "lightS" lightSBody

-- | Unfolding lemma for 'lightS'.
--
-- >>> runTPWith cvc5 lightSUnfold
-- Lemma: lightSUnfold                           Q.E.D.
-- [Proven] lightSUnfold :: Ɐt ∷ HTree → Bool
lightSUnfold :: TP (Proof (Forall "t" HTree -> SBool))
lightSUnfold = lemma "lightSUnfold"
    (\(Forall @"t" t) -> lightS t .== lightSBody t) []

-- | Body of 'light2W'.
light2WBody :: SHTree -> SInteger
light2WBody t = [sCase| t of
                   Tip w _ -> w
                   Bin l r | lightW l .<= lightW r -> smin (light2W l) (lightW r)
                           | True                  -> smin (lightW l) (light2W r)
                |]

-- | Weight of the second-lightest leaf.
light2W :: SHTree -> SInteger
light2W = smtFunction "light2W" light2WBody

-- | Unfolding lemma for 'light2W'.
--
-- >>> runTPWith cvc5 light2WUnfold
-- Lemma: light2WUnfold                          Q.E.D.
-- [Proven] light2WUnfold :: Ɐt ∷ HTree → Bool
light2WUnfold :: TP (Proof (Forall "t" HTree -> SBool))
light2WUnfold = lemma "light2WUnfold"
    (\(Forall @"t" t) -> light2W t .== light2WBody t) []

-- | Body of 'light2S'.
light2SBody :: SHTree -> SInteger
light2SBody t = [sCase| t of
                   Tip _ s -> s
                   Bin l r | lightW l .<= lightW r .&& light2W l .<= lightW r -> light2S l
                           | lightW l .<= lightW r                            -> lightS r
                           | lightW l .<= light2W r                           -> lightS l
                           | True                                             -> light2S r
                |]

-- | Symbol of the second-lightest leaf.
light2S :: SHTree -> SInteger
light2S = smtFunction "light2S" light2SBody

-- | Unfolding lemma for 'light2S'.
--
-- >>> runTPWith cvc5 light2SUnfold
-- Lemma: light2SUnfold                          Q.E.D.
-- [Proven] light2SUnfold :: Ɐt ∷ HTree → Bool
light2SUnfold :: TP (Proof (Forall "t" HTree -> SBool))
light2SUnfold = lemma "light2SUnfold"
    (\(Forall @"t" t) -> light2S t .== light2SBody t) []

-- | Body of 'deepW'.
deepWBody :: SHTree -> SInteger
deepWBody t = [sCase| t of
                 Tip w _ -> w
                 Bin l r | height l .>= height r -> deepW l
                         | True                  -> deepW r
              |]

-- | Weight of a leaf at maximum depth.
deepW :: SHTree -> SInteger
deepW = smtFunction "deepW" deepWBody

-- | Unfolding lemma for 'deepW'.
--
-- >>> runTPWith cvc5 deepWUnfold
-- Lemma: deepWUnfold                            Q.E.D.
-- [Proven] deepWUnfold :: Ɐt ∷ HTree → Bool
deepWUnfold :: TP (Proof (Forall "t" HTree -> SBool))
deepWUnfold = lemma "deepWUnfold"
    (\(Forall @"t" t) -> deepW t .== deepWBody t) []

-- | Body of 'deepS'.
deepSBody :: SHTree -> SInteger
deepSBody t = [sCase| t of
                 Tip _ s -> s
                 Bin l r | height l .>= height r -> deepS l
                         | True                  -> deepS r
              |]

-- | Symbol of a leaf at maximum depth.
deepS :: SHTree -> SInteger
deepS = smtFunction "deepS" deepSBody

-- | Unfolding lemma for 'deepS'.
--
-- >>> runTPWith cvc5 deepSUnfold
-- Lemma: deepSUnfold                            Q.E.D.
-- [Proven] deepSUnfold :: Ɐt ∷ HTree → Bool
deepSUnfold :: TP (Proof (Forall "t" HTree -> SBool))
deepSUnfold = lemma "deepSUnfold"
    (\(Forall @"t" t) -> deepS t .== deepSBody t) []

-- | Body of 'sibW'.
sibWBody :: SHTree -> SInteger
sibWBody t = [sCase| t of
                Tip w _ -> w
                Bin l r | height l .>= height r .&& height l .== 0 -> sweight r
                        | height l .>= height r                    -> sibW l
                        | height r .== 0                           -> sweight l
                        | True                                     -> sibW r
             |]

-- | Weight of the sibling of the deepest leaf.
sibW :: SHTree -> SInteger
sibW = smtFunction "sibW" sibWBody

-- | Unfolding lemma for 'sibW'.
--
-- >>> runTPWith cvc5 sibWUnfold
-- Lemma: sibWUnfold                             Q.E.D.
-- [Proven] sibWUnfold :: Ɐt ∷ HTree → Bool
sibWUnfold :: TP (Proof (Forall "t" HTree -> SBool))
sibWUnfold = lemma "sibWUnfold"
    (\(Forall @"t" t) -> sibW t .== sibWBody t) []

-- | Body of 'sibS'.
sibSBody :: SHTree -> SInteger
sibSBody t = [sCase| t of
                Tip _ s -> s
                Bin l r | height l .>= height r .&& height l .== 0 -> ssymbol r
                        | height l .>= height r                    -> sibS l
                        | height r .== 0                           -> ssymbol l
                        | True                                     -> sibS r
             |]

-- | Symbol of the sibling of the deepest leaf.
sibS :: SHTree -> SInteger
sibS = smtFunction "sibS" sibSBody

-- | Unfolding lemma for 'sibS'.
--
-- >>> runTPWith cvc5 sibSUnfold
-- Lemma: sibSUnfold                             Q.E.D.
-- [Proven] sibSUnfold :: Ɐt ∷ HTree → Bool
sibSUnfold :: TP (Proof (Forall "t" HTree -> SBool))
sibSUnfold = lemma "sibSUnfold"
    (\(Forall @"t" t) -> sibS t .== sibSBody t) []

-- | Body of 'relabelFrom'.
relabelFromBody :: SInteger -> SHTree -> SHTree
relabelFromBody n t = [sCase| t of
                         Tip w _ -> sTip w n
                         Bin l r -> sBin (relabelFrom n l)
                                         (relabelFrom (n + numLeaves l) r)
                      |]

-- | Relabel all leaves with consecutive integers starting from @n@.
relabelFrom :: SInteger -> SHTree -> SHTree
relabelFrom = smtFunction "relabelFrom" relabelFromBody

-- | Unfolding lemma for 'relabelFrom'.
--
-- >>> runTPWith cvc5 relabelFromUnfold
-- Lemma: relabelFromUnfold                      Q.E.D.
-- [Proven] relabelFromUnfold :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelFromUnfold :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelFromUnfold = lemma "relabelFromUnfold"
    (\(Forall @"n" n) (Forall @"t" t) -> relabelFrom n t .== relabelFromBody n t) []

-- ** Optimal merge

-- | Body of 'optMerge'.
optMergeBody :: SHTree -> SHTree
optMergeBody t = let t'  = relabelFrom 0 t

                     lw  = lightW t'
                     ls  = lightS t'

                     l2w = light2W t'
                     l2s = light2S t'

                     cw  = deepW t'
                     cs  = deepS t'

                     dw  = sibW t'
                     ds  = sibS t'

                     swapped = ite (lw .== dw .&& ls .== ds)
                                   (swap l2w l2s cw cs t')
                                   (ite (l2w .== cw .&& l2s .== cs)
                                        (swap lw ls dw ds t')
                                        (swap l2w l2s dw ds (swap lw ls cw cs t')))
                 in collapse swapped

-- | Optimal merge: relabel, swap the two lightest to the deepest positions, then collapse.
optMerge :: SHTree -> SHTree
optMerge = smtFunction "optMerge" optMergeBody

-- | Unfolding lemma for 'optMerge'.
--
-- >>> runTPWith cvc5 optMergeUnfold
-- Lemma: optMergeUnfold                         Q.E.D.
-- [Proven] optMergeUnfold :: Ɐt ∷ HTree → Bool
optMergeUnfold :: TP (Proof (Forall "t" HTree -> SBool))
optMergeUnfold = lemma "optMergeUnfold"
    (\(Forall @"t" t) -> optMerge t .== optMergeBody t) []

-- ** Basic structural lemmas

-- | Height is non-negative.
--
-- >>> runTPWith cvc5 heightNonNeg
-- Lemma: heightNonNeg                           Q.E.D.
-- Functions proven terminating: height
-- [Proven] heightNonNeg :: Ɐt ∷ HTree → Bool
heightNonNeg :: TP (Proof (Forall "t" HTree -> SBool))
heightNonNeg = inductiveLemma "heightNonNeg" (\(Forall @"t" t) -> height t .>= 0) []

-- | Number of leaves is at least 1.
--
-- >>> runTPWith cvc5 numLeavesPos
-- Lemma: numLeavesPos                           Q.E.D.
-- Functions proven terminating: numLeaves
-- [Proven] numLeavesPos :: Ɐt ∷ HTree → Bool
numLeavesPos :: TP (Proof (Forall "t" HTree -> SBool))
numLeavesPos = inductiveLemma "numLeavesPos" (\(Forall @"t" t) -> numLeaves t .>= 1) []

-- ** Relabeling preservation lemmas

-- | Relabeling preserves tree size.
--
-- >>> runTPWith cvc5 relabelTreeSize
-- Lemma: relabelFromUnfold                     Q.E.D.
-- Lemma: treeSizePos                           Q.E.D.
-- Inductive lemma (strong): relabelTreeSize
--   Step: Measure is non-negative              Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                Q.E.D.
--     Step: 1.2.1                              Q.E.D.
--     Step: 1.2.2                              Q.E.D.
--     Step: 1.Completeness                     Q.E.D.
--   Result:                                    Q.E.D.
-- Functions proven terminating: numLeaves, relabelFrom, treeSize
-- [Proven] relabelTreeSize :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelTreeSize :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelTreeSize = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos

   sInduct "relabelTreeSize"
       (\(Forall @"n" n) (Forall @"t" t) -> treeSize (relabelFrom n t) .== treeSize t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- treeSize (relabelFrom n t)
         =: [pCase| t of
               Tip{}   -> trivial
               Bin l r -> treeSize (relabelFrom n t)
                       ?? rfU `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: treeSize t
                       =: qed
            |]

-- | Relabeling preserves number of leaves.
--
-- >>> runTPWith cvc5 relabelNumLeaves
-- Lemma: relabelFromUnfold                      Q.E.D.
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
relabelNumLeaves :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelNumLeaves = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos

   sInduct "relabelNumLeaves"
       (\(Forall @"n" n) (Forall @"t" t) -> numLeaves (relabelFrom n t) .== numLeaves t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- numLeaves (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> numLeaves (relabelFrom n t)
                       ?? rfU   `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: numLeaves t
                       =: qed
            |]

-- | Relabeling preserves height.
--
-- >>> runTPWith cvc5 relabelHeight
-- Lemma: relabelFromUnfold                   Q.E.D.
-- Lemma: treeSizePos                         Q.E.D.
-- Inductive lemma (strong): relabelHeight
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: height, numLeaves, relabelFrom, treeSize
-- [Proven] relabelHeight :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelHeight :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelHeight = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos

   sInduct "relabelHeight"
       (\(Forall @"n" n) (Forall @"t" t) -> height (relabelFrom n t) .== height t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- height (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> height (relabelFrom n t)
                       ?? rfU   `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: height t
                       =: qed
            |]

-- | Relabeling preserves tree weight.
--
-- >>> runTPWith cvc5 relabelTreeWeight
-- Lemma: relabelFromUnfold                       Q.E.D.
-- Lemma: treeSizePos                             Q.E.D.
-- Inductive lemma (strong): relabelTreeWeight
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                  Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2                                Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: numLeaves, relabelFrom, treeSize, treeWeight
-- [Proven] relabelTreeWeight :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelTreeWeight :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelTreeWeight = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos

   sInduct "relabelTreeWeight"
       (\(Forall @"n" n) (Forall @"t" t) -> treeWeight (relabelFrom n t) .== treeWeight t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- treeWeight (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> treeWeight (relabelFrom n t)
                       ?? rfU   `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: treeWeight t
                       =: qed
            |]

-- | Relabeling preserves cost.
--
-- >>> runTPWith cvc5 relabelCost
-- Lemma: relabelFromUnfold                       Q.E.D.
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: relabelTreeWeight                       Q.E.D.
-- Inductive lemma (strong): relabelCost
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                  Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2                                Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: cost, numLeaves, relabelFrom, treeSize, treeWeight
-- [Proven] relabelCost :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelCost :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelCost = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos
   rlTW  <- recall relabelTreeWeight

   sInduct "relabelCost"
       (\(Forall @"n" n) (Forall @"t" t) -> cost (relabelFrom n t) .== cost t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- cost (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> cost (relabelFrom n t)
                       ?? rfU   `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? rlTW  `at` (Inst @"n" n, Inst @"t" l)
                       ?? rlTW  `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: cost t
                       =: qed
            |]

-- | Relabeling preserves lightW.
--
-- >>> runTPWith cvc5 relabelLightW
-- Lemma: relabelFromUnfold                   Q.E.D.
-- Lemma: treeSizePos                         Q.E.D.
-- Inductive lemma (strong): relabelLightW
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                              Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: lightW, numLeaves, relabelFrom, treeSize
-- [Proven] relabelLightW :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelLightW :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelLightW = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos

   sInduct "relabelLightW"
       (\(Forall @"n" n) (Forall @"t" t) -> lightW (relabelFrom n t) .== lightW t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- lightW (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> lightW (relabelFrom n t)
                       ?? rfU   `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: lightW t
                       =: qed
            |]

-- | Relabeling preserves light2W.
--
-- >>> runTPWith cvc5 relabelLight2W
-- Lemma: relabelFromUnfold                    Q.E.D.
-- Lemma: treeSizePos                          Q.E.D.
-- Lemma: relabelLightW                        Q.E.D.
-- Inductive lemma (strong): relabelLight2W
--   Step: Measure is non-negative             Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                               Q.E.D.
--     Step: 1.2.1                             Q.E.D.
--     Step: 1.2.2                             Q.E.D.
--     Step: 1.Completeness                    Q.E.D.
--   Result:                                   Q.E.D.
-- Functions proven terminating: light2W, lightW, numLeaves, relabelFrom, treeSize
-- [Proven] relabelLight2W :: Ɐn ∷ Integer → Ɐt ∷ HTree → Bool
relabelLight2W :: TP (Proof (Forall "n" Integer -> Forall "t" HTree -> SBool))
relabelLight2W = do
   rfU   <- recall relabelFromUnfold
   tsPos <- recall treeSizePos
   rlLW  <- recall relabelLightW

   sInduct "relabelLight2W"
       (\(Forall @"n" n) (Forall @"t" t) -> light2W (relabelFrom n t) .== light2W t)
       (\_ t -> treeSize t, [proofOf tsPos]) $
       \ih n t -> []
         |- light2W (relabelFrom n t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> light2W (relabelFrom n t)
                       ?? rfU   `at` (Inst @"n" n, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"n" n, Inst @"t" l)
                       ?? ih    `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       ?? rlLW  `at` (Inst @"n" n, Inst @"t" l)
                       ?? rlLW  `at` (Inst @"n" (n + numLeaves l), Inst @"t" r)
                       =: light2W t
                       =: qed
            |]

-- ** Swap preservation lemmas

-- | Swap preserves tree size.
--
-- >>> runTPWith cvc5 swapTreeSize
-- Lemma: swapUnfold                         Q.E.D.
-- Lemma: treeSizePos                        Q.E.D.
-- Inductive lemma (strong): swapTreeSize
--   Step: Measure is non-negative           Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                           Q.E.D.
--     Step: 1.1.2                           Q.E.D.
--     Step: 1.2.1                           Q.E.D.
--     Step: 1.2.2                           Q.E.D.
--     Step: 1.Completeness                  Q.E.D.
--   Result:                                 Q.E.D.
-- Functions proven terminating: swap, treeSize
-- [Proven] swapTreeSize :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapTreeSize :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapTreeSize = do
   swU   <- recall swapUnfold
   tsPos <- recall treeSizePos

   sInduct "swapTreeSize"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           treeSize (swap wa sa wb sb t) .== treeSize t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> []
         |- treeSize (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{} -> treeSize (swap wa sa wb sb t)
                      ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                      =: treeSize t
                      =: qed
               Bin l r -> treeSize (swap wa sa wb sb t)
                       ?? swU   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: treeSize t
                       =: qed
            |]

-- | Swap preserves number of leaves.
--
-- >>> runTPWith cvc5 swapNumLeaves
-- Lemma: swapUnfold                          Q.E.D.
-- Lemma: treeSizePos                         Q.E.D.
-- Inductive lemma (strong): swapNumLeaves
--   Step: Measure is non-negative            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                            Q.E.D.
--     Step: 1.1.2                            Q.E.D.
--     Step: 1.2.1                            Q.E.D.
--     Step: 1.2.2                            Q.E.D.
--     Step: 1.Completeness                   Q.E.D.
--   Result:                                  Q.E.D.
-- Functions proven terminating: numLeaves, swap, treeSize
-- [Proven] swapNumLeaves :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapNumLeaves :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapNumLeaves = do
   swU   <- recall swapUnfold
   tsPos <- recall treeSizePos

   sInduct "swapNumLeaves"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           numLeaves (swap wa sa wb sb t) .== numLeaves t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> []
         |- numLeaves (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{} -> numLeaves (swap wa sa wb sb t)
                      ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                      =: numLeaves t
                      =: qed
               Bin l r -> numLeaves (swap wa sa wb sb t)
                       ?? swU   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: numLeaves t
                       =: qed
            |]

-- | Swap preserves height.
--
-- >>> runTPWith cvc5 swapHeight
-- Lemma: swapUnfold                       Q.E.D.
-- Lemma: treeSizePos                      Q.E.D.
-- Inductive lemma (strong): swapHeight
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: height, swap, treeSize
-- [Proven] swapHeight :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapHeight :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapHeight = do
   swU   <- recall swapUnfold
   tsPos <- recall treeSizePos

   sInduct "swapHeight"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           height (swap wa sa wb sb t) .== height t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> []
         |- height (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> height (swap wa sa wb sb t)
                       ?? swU   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: height t
                       =: qed
            |]

-- ** Swap and treeWeight (unique leaves)

-- | countWS is non-negative.
--
-- >>> runTPWith cvc5 countWSNonNeg
-- [Proven] countWSNonNeg :: Ɐw ∷ Integer → Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
countWSNonNeg :: TP (Proof (Forall "w" Integer -> Forall "s" Integer -> Forall "t" HTree -> SBool))
countWSNonNeg = do
   cwU   <- recall countWSUnfold
   tsPos <- recall treeSizePos

   sInduct "countWSNonNeg"
       (\(Forall @"w" w) (Forall @"s" s) (Forall @"t" t) -> countWS w s t .>= 0)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih w s t -> []
         |- countWS w s t .>= (0 :: SInteger)
         =: [pCase| t of
               Tip{} -> countWS w s t .>= (0 :: SInteger)
                     ?? cwU `at` (Inst @"w" w, Inst @"s" s, Inst @"t" t)
                     =: sTrue
                     =: qed
               Bin l r -> countWS w s t .>= (0 :: SInteger)
                       ?? cwU   `at` (Inst @"w" w, Inst @"s" s, Inst @"t" t)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"t" l)
                       ?? ih    `at` (Inst @"w" w, Inst @"s" s, Inst @"t" r)
                       =: sTrue
                       =: qed
            |]

-- | Swap is the identity when neither pair appears in the tree.
--
-- >>> runTPWith cvc5 swapIdentity
-- [Proven] swapIdentity :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapIdentity :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapIdentity = do
   swU   <- recall swapUnfold
   cwU   <- recall countWSUnfold
   cwNN  <- recall countWSNonNeg
   tsPos <- recall treeSizePos

   sInduct "swapIdentity"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           countWS wa sa t .== 0 .&& countWS wb sb t .== 0
           .=> swap wa sa wb sb t .== t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> [countWS wa sa t .== 0, countWS wb sb t .== 0]
         |- swap wa sa wb sb t
         =: [pCase| t of
               Tip{} -> swap wa sa wb sb t
                       ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       =: t
                       =: qed
               Bin l r -> swap wa sa wb sb t
                       ?? swU  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: t
                       =: qed
            |]

-- | When exactly one leaf matches (wa,sa) and none match (wb,sb),
-- swap changes treeWeight by exactly @(wb - wa)@. Note: all linear arithmetic.
--
-- >>> runTPWith cvc5 swapSingleTW
-- [Proven] swapSingleTW :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapSingleTW :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapSingleTW = do
   swU   <- recall swapUnfold
   cwU   <- recall countWSUnfold
   cwNN  <- recall countWSNonNeg
   swId  <- recall swapIdentity
   tsPos <- recall treeSizePos

   sInduct "swapSingleTW"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           countWS wa sa t .== 1 .&& countWS wb sb t .== 0
           .=> treeWeight (swap wa sa wb sb t) .== treeWeight t + (wb - wa))
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> [countWS wa sa t .== 1, countWS wb sb t .== 0]
         |- treeWeight (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{} -> treeWeight (swap wa sa wb sb t)
                       ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       =: treeWeight t + (wb - wa)
                       =: qed
               Bin l r -> treeWeight (swap wa sa wb sb t)
                       ?? swU  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? swId `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? swId `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: treeWeight t + (wb - wa)
                       =: qed
            |]

-- | Reverse of 'swapSingleTW': when no leaf matches (wa,sa) but one matches (wb,sb),
-- swap changes treeWeight by @(wa - wb)@.
--
-- >>> runTPWith cvc5 swapSingleTWRev
-- [Proven] swapSingleTWRev :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapSingleTWRev :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapSingleTWRev = do
   swU   <- recall swapUnfold
   cwU   <- recall countWSUnfold
   cwNN  <- recall countWSNonNeg
   swId  <- recall swapIdentity
   tsPos <- recall treeSizePos

   sInduct "swapSingleTWRev"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           countWS wa sa t .== 0 .&& countWS wb sb t .== 1
           .=> treeWeight (swap wa sa wb sb t) .== treeWeight t + (wa - wb))
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> [countWS wa sa t .== 0, countWS wb sb t .== 1]
         |- treeWeight (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{} -> treeWeight (swap wa sa wb sb t)
                       ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       =: treeWeight t + (wa - wb)
                       =: qed
               Bin l r -> treeWeight (swap wa sa wb sb t)
                       ?? swU  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? swId  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? swId  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: treeWeight t + (wa - wb)
                       =: qed
            |]

-- | Swap preserves treeWeight when each pair appears exactly once.
-- All arithmetic is linear since countWS values are known constants (0 or 1).
--
-- >>> runTPWith cvc5 swapUniqueTW
-- [Proven] swapUniqueTW :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapUniqueTW :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapUniqueTW = do
   swU     <- recall swapUnfold
   cwU     <- recall countWSUnfold
   cwNN    <- recall countWSNonNeg
   swId    <- recall swapIdentity
   swSing  <- recall swapSingleTW
   swSingR <- recall swapSingleTWRev
   tsPos   <- recall treeSizePos

   sInduct "swapUniqueTW"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           countWS wa sa t .== 1 .&& countWS wb sb t .== 1
           .=> treeWeight (swap wa sa wb sb t) .== treeWeight t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> [countWS wa sa t .== 1, countWS wb sb t .== 1]
         |- treeWeight (swap wa sa wb sb t)
         =: [pCase| t of
               Tip{} -> treeWeight (swap wa sa wb sb t)
                       ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       =: treeWeight t
                       =: qed
               Bin l r -> treeWeight (swap wa sa wb sb t)
                       ?? swU  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                       ?? cwNN `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                       =: cases
                            [ countWS wa sa l .>= 1 .&& countWS wb sb l .>= 1
                                ==> treeWeight (swap wa sa wb sb t)
                                 ?? cwU   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                                 ?? cwU   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                                 ?? cwNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                 ?? cwNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                 ?? tsPos `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                 ?? swId  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                 =: treeWeight t
                                 =: qed

                            , countWS wa sa l .>= 1 .&& sNot (countWS wb sb l .>= 1)
                                ==> treeWeight (swap wa sa wb sb t)
                                 ?? cwU    `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                                 ?? cwU    `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                                 ?? cwNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                 ?? cwNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                 ?? cwNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                 ?? tsPos  `at` Inst @"t" l
                                 ?? tsPos  `at` Inst @"t" r
                                 ?? swSing  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                 ?? swSingR `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                 =: treeWeight t
                                 =: qed

                            , sNot (countWS wa sa l .>= 1) .&& countWS wb sb l .>= 1
                                ==> treeWeight (swap wa sa wb sb t)
                                 ?? cwU    `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                                 ?? cwU    `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                                 ?? cwNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                                 ?? cwNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                                 ?? cwNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                                 ?? tsPos  `at` Inst @"t" l
                                 ?? tsPos  `at` Inst @"t" r
                                 ?? swSingR `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                 ?? swSing  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                 =: treeWeight t
                                 =: qed

                            , sNot (countWS wa sa l .>= 1) .&& sNot (countWS wb sb l .>= 1)
                                ==> treeWeight (swap wa sa wb sb t)
                                 ?? cwU   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                                 ?? cwU   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                                 ?? cwNN  `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                                 ?? cwNN  `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                                 ?? tsPos `at` Inst @"t" l
                                 ?? tsPos `at` Inst @"t" r
                                 ?? swId  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                                 ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                                 =: treeWeight t
                                 =: qed
                            ]
            |]

-- ** Collapse properties

-- | A tree with height 0 has tree size 1 (i.e., it's a Tip).
--
-- >>> runTPWith cvc5 heightZeroTreeSizeOne
-- [Proven] heightZeroTreeSizeOne :: Ɐt ∷ HTree → Bool
heightZeroTreeSizeOne :: TP (Proof (Forall "t" HTree -> SBool))
heightZeroTreeSizeOne = do
   hNN <- recall heightNonNeg

   inductiveLemma "heightZeroTreeSizeOne"
       (\(Forall @"t" t) -> height t .== 0 .=> treeSize t .== 1)
       [proofOf hNN]

-- | Collapsing a tree with positive height reduces tree size by 2.
--
-- >>> runTPWith cvc5 collapseTreeSize
-- Lemma: treeSizePos                            Q.E.D.
-- Lemma: heightNonNeg                           Q.E.D.
-- Lemma: collapseUnfold                         Q.E.D.
-- Lemma: heightZeroTreeSizeOne                  Q.E.D.
-- Inductive lemma (strong): collapseTreeSize
--   Step: Measure is non-negative               Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                 Q.E.D.
--     Step: 1.2.1                               Q.E.D.
--     Step: 1.2.2                               Q.E.D.
--     Step: 1.Completeness                      Q.E.D.
--   Result:                                     Q.E.D.
-- Functions proven terminating: collapse, height, treeSize, treeWeight
-- [Proven] collapseTreeSize :: Ɐt ∷ HTree → Bool
collapseTreeSize :: TP (Proof (Forall "t" HTree -> SBool))
collapseTreeSize = do
   tsPos <- recall treeSizePos
   hNN   <- recall heightNonNeg
   colU  <- recall collapseUnfold
   hz1   <- recall heightZeroTreeSizeOne

   sInduct "collapseTreeSize"
       (\(Forall @"t" t) -> height t .> 0 .=> treeSize (collapse t) + 2 .== treeSize t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [height t .> 0]
         |- treeSize (collapse t) + 2
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> treeSize (collapse t) + 2
                       ?? colU  `at` Inst @"t" t
                       ?? hNN   `at` Inst @"t" l
                       ?? hNN   `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? hz1   `at` Inst @"t" l
                       ?? hz1   `at` Inst @"t" r
                       ?? ih    `at` Inst @"t" l
                       ?? ih    `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" (sleft l)
                       ?? tsPos `at` Inst @"t" (sright l)
                       ?? tsPos `at` Inst @"t" (sleft r)
                       ?? tsPos `at` Inst @"t" (sright r)
                       =: treeSize t
                       =: qed
            |]

-- | Collapsing a tree with positive height reduces leaf count by 1.
--
-- >>> runTPWith cvc5 collapseNumLeaves
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: heightNonNeg                            Q.E.D.
-- Lemma: numLeavesPos                            Q.E.D.
-- Lemma: collapseUnfold                          Q.E.D.
-- Lemma: heightZeroTreeSizeOne                   Q.E.D.
-- Inductive lemma (strong): collapseNumLeaves
--   Step: Measure is non-negative                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                  Q.E.D.
--     Step: 1.2.1                                Q.E.D.
--     Step: 1.2.2                                Q.E.D.
--     Step: 1.Completeness                       Q.E.D.
--   Result:                                      Q.E.D.
-- Functions proven terminating: collapse, height, numLeaves, treeSize, treeWeight
-- [Proven] collapseNumLeaves :: Ɐt ∷ HTree → Bool
collapseNumLeaves :: TP (Proof (Forall "t" HTree -> SBool))
collapseNumLeaves = do
   tsPos <- recall treeSizePos
   hNN   <- recall heightNonNeg
   nlPos <- recall numLeavesPos
   colU  <- recall collapseUnfold
   hz1   <- recall heightZeroTreeSizeOne

   sInduct "collapseNumLeaves"
       (\(Forall @"t" t) -> height t .> 0 .=> numLeaves (collapse t) + 1 .== numLeaves t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [height t .> 0]
         |- numLeaves (collapse t) + 1
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> numLeaves (collapse t) + 1
                       ?? colU  `at` Inst @"t" t
                       ?? hNN   `at` Inst @"t" l
                       ?? hNN   `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? nlPos `at` Inst @"t" l
                       ?? nlPos `at` Inst @"t" r
                       ?? hz1   `at` Inst @"t" l
                       ?? hz1   `at` Inst @"t" r
                       ?? ih    `at` Inst @"t" l
                       ?? ih    `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" (sleft l)
                       ?? tsPos `at` Inst @"t" (sright l)
                       ?? tsPos `at` Inst @"t" (sleft r)
                       ?? tsPos `at` Inst @"t" (sright r)
                       =: numLeaves t
                       =: qed
            |]

-- | Collapse preserves tree weight.
--
-- >>> runTPWith cvc5 collapseTreeWeight
-- Lemma: treeSizePos                              Q.E.D.
-- Lemma: heightNonNeg                             Q.E.D.
-- Lemma: collapseUnfold                           Q.E.D.
-- Lemma: heightZeroTreeSizeOne                    Q.E.D.
-- Inductive lemma (strong): collapseTreeWeight
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                   Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: collapse, height, treeSize, treeWeight
-- [Proven] collapseTreeWeight :: Ɐt ∷ HTree → Bool
collapseTreeWeight :: TP (Proof (Forall "t" HTree -> SBool))
collapseTreeWeight = do
   tsPos <- recall treeSizePos
   hNN   <- recall heightNonNeg
   colU  <- recall collapseUnfold
   hz1   <- recall heightZeroTreeSizeOne

   sInduct "collapseTreeWeight"
       (\(Forall @"t" t) -> height t .> 0 .=> treeWeight (collapse t) .== treeWeight t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [height t .> 0]
         |- treeWeight (collapse t)
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> treeWeight (collapse t)
                       ?? colU  `at` Inst @"t" t
                       ?? hNN   `at` Inst @"t" l
                       ?? hNN   `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? hz1   `at` Inst @"t" l
                       ?? hz1   `at` Inst @"t" r
                       ?? ih    `at` Inst @"t" l
                       ?? ih    `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" (sleft l)
                       ?? tsPos `at` Inst @"t" (sright l)
                       ?? tsPos `at` Inst @"t" (sleft r)
                       ?? tsPos `at` Inst @"t" (sright r)
                       =: treeWeight t
                       =: qed
            |]

-- | Cost decomposition for collapse: collapsing removes the deepest pair's weight contribution.
--
-- >>> runTPWith cvc5 costDecomp
-- Lemma: treeSizePos                              Q.E.D.
-- Lemma: heightNonNeg                             Q.E.D.
-- Lemma: collapseUnfold                           Q.E.D.
-- Lemma: heightZeroTreeSizeOne                    Q.E.D.
-- Lemma: collapseTreeWeight                       Q.E.D.
-- Inductive lemma (strong): costDecomp
--   Step: Measure is non-negative                 Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                   Q.E.D.
--     Step: 1.2.1                                 Q.E.D.
--     Step: 1.2.2                                 Q.E.D.
--     Step: 1.Completeness                        Q.E.D.
--   Result:                                       Q.E.D.
-- Functions proven terminating: collapse, cost, deepW, height, sibW, treeSize, treeWeight
-- [Proven] costDecomp :: Ɐt ∷ HTree → Bool
costDecomp :: TP (Proof (Forall "t" HTree -> SBool))
costDecomp = do
   tsPos <- recall treeSizePos
   hNN   <- recall heightNonNeg
   colU  <- recall collapseUnfold
   hz1   <- recall heightZeroTreeSizeOne
   colTW <- recall collapseTreeWeight

   sInduct "costDecomp"
       (\(Forall @"t" t) -> height t .> 0 .=> cost (collapse t) + deepW t + sibW t .== cost t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [height t .> 0]
         |- cost (collapse t) + deepW t + sibW t
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> cost (collapse t) + deepW t + sibW t
                       ?? colU  `at` Inst @"t" t
                       ?? hNN   `at` Inst @"t" l
                       ?? hNN   `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? hz1   `at` Inst @"t" l
                       ?? hz1   `at` Inst @"t" r
                       ?? colTW `at` Inst @"t" l
                       ?? colTW `at` Inst @"t" r
                       ?? ih    `at` Inst @"t" l
                       ?? ih    `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" (sleft l)
                       ?? tsPos `at` Inst @"t" (sright l)
                       ?? tsPos `at` Inst @"t" (sleft r)
                       ?? tsPos `at` Inst @"t" (sright r)
                       =: cost t
                       =: qed
            |]

-- | After swapping (wa,sa) with the deepest leaf, deepW becomes wa.
-- This works because swap preserves height, so deepW still looks at
-- the same position, which now holds (wa,sa).
--
-- >>> runTPWith cvc5 swapDeepW
-- [Proven] swapDeepW :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐt ∷ HTree → Bool
swapDeepW :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "t" HTree -> SBool))
swapDeepW = do
   swU   <- recall swapUnfold
   swHt  <- recall swapHeight
   dwU   <- recall deepWUnfold
   hNN   <- recall heightNonNeg
   tsPos <- recall treeSizePos

   sInduct "swapDeepW"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"t" t) ->
           deepW (swap wa sa (deepW t) (deepS t) t) .== wa)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa t -> []
         |- deepW (swap wa sa (deepW t) (deepS t) t)
         =: [pCase| t of
               Tip{} -> deepW (swap wa sa (deepW t) (deepS t) t)
                     ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" t)
                     ?? dwU `at` Inst @"t" t
                     =: wa
                     =: qed
               Bin l r -> deepW (swap wa sa (deepW t) (deepS t) t)
                       ?? swU  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" t)
                       ?? swHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                       ?? swHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                       ?? hNN  `at` Inst @"t" l
                       ?? hNN  `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" l)
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" r)
                       =: wa
                       =: qed
            |]

-- | Replacing a heavier leaf with a lighter one does not increase cost.
-- When @wa <= wb@ and only (wb,sb) appears (to be replaced by (wa,sa)),
-- cost decreases because lighter weight at each level reduces cost.
-- All arithmetic is linear.
--
-- >>> runTPWith cvc5 swapLighterCost
-- [Proven] swapLighterCost :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐwb ∷ Integer → Ɐsb ∷ Integer → Ɐt ∷ HTree → Bool
swapLighterCost :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "wb" Integer -> Forall "sb" Integer -> Forall "t" HTree -> SBool))
swapLighterCost = do
   swU    <- recall swapUnfold
   cwU    <- recall countWSUnfold
   cwNN   <- recall countWSNonNeg
   swId   <- recall swapIdentity
   swSingR <- recall swapSingleTWRev
   tsPos  <- recall treeSizePos

   sInduct "swapLighterCost"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"wb" wb) (Forall @"sb" sb) (Forall @"t" t) ->
           wa .<= wb .&& countWS wa sa t .== 0 .&& countWS wb sb t .== 1
           .=> cost (swap wa sa wb sb t) .<= cost t)
       (\_ _ _ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa wb sb t -> [wa .<= wb, countWS wa sa t .== 0, countWS wb sb t .== 1]
         |- cost (swap wa sa wb sb t) .<= cost t
         =: [pCase| t of
               Tip{} -> trivial
               Bin l r -> cost (swap wa sa wb sb t) .<= cost t
                       ?? swU    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" t)
                       ?? cwU    `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" t)
                       ?? cwU    `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" t)
                       ?? cwNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" l)
                       ?? cwNN   `at` (Inst @"w" wa, Inst @"s" sa, Inst @"t" r)
                       ?? cwNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" l)
                       ?? cwNN   `at` (Inst @"w" wb, Inst @"s" sb, Inst @"t" r)
                       ?? tsPos  `at` Inst @"t" l
                       ?? tsPos  `at` Inst @"t" r
                       ?? ih     `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? ih     `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? swId   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? swId   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       ?? swSingR `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" l)
                       ?? swSingR `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" wb, Inst @"sb" sb, Inst @"t" r)
                       =: sTrue
                       =: qed
            |]

-- | After swapping (wa,sa) with the deepest leaf, deepS becomes sa.
--
-- >>> runTPWith cvc5 swapDeepS
-- [Proven] swapDeepS :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐt ∷ HTree → Bool
swapDeepS :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "t" HTree -> SBool))
swapDeepS = do
   swU   <- recall swapUnfold
   swHt  <- recall swapHeight
   dsU   <- recall deepSUnfold
   hNN   <- recall heightNonNeg
   tsPos <- recall treeSizePos

   sInduct "swapDeepS"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"t" t) ->
           deepS (swap wa sa (deepW t) (deepS t) t) .== sa)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa t -> []
         |- deepS (swap wa sa (deepW t) (deepS t) t)
         =: [pCase| t of
               Tip{} -> deepS (swap wa sa (deepW t) (deepS t) t)
                     ?? swU `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" t)
                     ?? dsU `at` Inst @"t" t
                     =: sa
                     =: qed
               Bin l r -> deepS (swap wa sa (deepW t) (deepS t) t)
                       ?? swU  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" t)
                       ?? swHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" l)
                       ?? swHt `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" r)
                       ?? hNN  `at` Inst @"t" l
                       ?? hNN  `at` Inst @"t" r
                       ?? tsPos `at` Inst @"t" l
                       ?? tsPos `at` Inst @"t" r
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" l)
                       ?? ih   `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" r)
                       =: sa
                       =: qed
            |]

-- | Swapping a lighter leaf with the deepest leaf does not increase cost.
-- The "both in same subtree" case follows from the IH. The "one in each" case
-- requires depth reasoning (non-linear arithmetic) — sorry for now.
--
-- >>> runTPWith cvc5 swapDeepCost
-- [Modulo: sorry] swapDeepCost :: Ɐwa ∷ Integer → Ɐsa ∷ Integer → Ɐt ∷ HTree → Bool
swapDeepCost :: TP (Proof (Forall "wa" Integer -> Forall "sa" Integer -> Forall "t" HTree -> SBool))
swapDeepCost = do
   swLC  <- recall swapLighterCost
   tsPos <- recall treeSizePos

   sInduct "swapDeepCost"
       (\(Forall @"wa" wa) (Forall @"sa" sa) (Forall @"t" t) ->
           wa .<= deepW t .&& countWS wa sa t .== 1 .&& countWS (deepW t) (deepS t) t .== 1
           .=> cost (swap wa sa (deepW t) (deepS t) t) .<= cost t)
       (\_ _ t -> treeSize t, [proofOf tsPos]) $
       \ih wa sa t -> [wa .<= deepW t, countWS wa sa t .== 1, countWS (deepW t) (deepS t) t .== 1]
         |- cost (swap wa sa (deepW t) (deepS t) t) .<= cost t
         ?? swLC  `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"wb" (deepW t), Inst @"sb" (deepS t), Inst @"t" t)
         ?? tsPos `at` Inst @"t" t
         ?? ih    `at` (Inst @"wa" wa, Inst @"sa" sa, Inst @"t" t)
         ?? sorry
         =: sTrue
         =: qed

-- ** OptMerge cost bound

-- | OptMerge cost bound: the greedy exchange doesn't increase cost.
--
-- >>> runTPWith cvc5 optMergeCost
-- [Proven] optMergeCost :: Ɐt ∷ HTree → Bool
optMergeCost :: TP (Proof (Forall "t" HTree -> SBool))
optMergeCost = do
   omU    <- recall optMergeUnfold
   rlCost <- recall relabelCost
   rlLW   <- recall relabelLightW
   rlL2W  <- recall relabelLight2W
   rlHt   <- recall relabelHeight
   rlNL   <- recall relabelNumLeaves
   rlTW   <- recall relabelTreeWeight
   cd     <- recall costDecomp
   hNN    <- recall heightNonNeg
   nlPos  <- recall numLeavesPos
   swDW   <- recall swapDeepW
   swDS   <- recall swapDeepS
   swDC   <- recall swapDeepCost

   calc "optMergeCost"
       (\(Forall @"t" t) ->
           numLeaves t .>= 3 .=> cost (optMerge t) + lightW t + light2W t .<= cost t) $
       \t -> let t' = relabelFrom 0 t
             in [numLeaves t .>= 3]
         |- cost (optMerge t) + lightW t + light2W t .<= cost t
         ?? omU    `at` Inst @"t" t
         ?? rlCost `at` (Inst @"n" 0, Inst @"t" t)
         ?? rlLW   `at` (Inst @"n" 0, Inst @"t" t)
         ?? rlL2W  `at` (Inst @"n" 0, Inst @"t" t)
         ?? rlHt   `at` (Inst @"n" 0, Inst @"t" t)
         ?? rlNL   `at` (Inst @"n" 0, Inst @"t" t)
         ?? rlTW   `at` (Inst @"n" 0, Inst @"t" t)
         ?? hNN    `at` Inst @"t" t'
         ?? nlPos  `at` Inst @"t" t'
         ?? cd     `at` Inst @"t" (optMergeBody t)
         ?? swDW   `at` (Inst @"wa" (lightW t'), Inst @"sa" (lightS t'), Inst @"t" t')
         ?? swDS   `at` (Inst @"wa" (lightW t'), Inst @"sa" (lightS t'), Inst @"t" t')
         ?? swDC   `at` (Inst @"wa" (lightW t'), Inst @"sa" (lightS t'), Inst @"t" t')
         ?? sorry
         =: sTrue
         =: qed

-- ** OptMerge structural properties

-- | OptMerge reduces tree size (needed for the induction measure).
--
-- >>> runTPWith cvc5 optMergeTreeSize
-- Lemma: optMergeUnfold                         Q.E.D.
-- Lemma: treeSizePos                            Q.E.D.
-- Lemma: heightNonNeg                           Q.E.D.
-- Lemma: numLeavesPos                           Q.E.D.
-- Lemma: relabelTreeSize                        Q.E.D.
-- Lemma: relabelHeight                          Q.E.D.
-- Lemma: relabelNumLeaves                       Q.E.D.
-- Lemma: swapTreeSize                           Q.E.D.
-- Lemma: swapHeight                             Q.E.D.
-- Lemma: collapseTreeSize                       Q.E.D.
-- Lemma: optMergeTreeSize                       Q.E.D.
-- Functions proven terminating:
--   collapse, deepS, deepW, height, light2S, light2W, lightS, lightW, numLeaves, optMerge,
--   relabelFrom, sibS, sibW, swap, treeSize, treeWeight
-- [Proven] optMergeTreeSize :: Ɐt ∷ HTree → Bool
optMergeTreeSize :: TP (Proof (Forall "t" HTree -> SBool))
optMergeTreeSize = do
   omU    <- recall optMergeUnfold
   tsPos  <- recall treeSizePos
   hNN    <- recall heightNonNeg
   nlPos  <- recall numLeavesPos
   rlTS   <- recall relabelTreeSize
   rlHt   <- recall relabelHeight
   rlNL   <- recall relabelNumLeaves
   swTS   <- recall swapTreeSize
   swHt   <- recall swapHeight
   collTS <- recall collapseTreeSize

   lemma "optMergeTreeSize"
       (\(Forall @"t" t) -> numLeaves t .>= 3 .=> treeSize (optMerge t) .< treeSize t)
              [ proofOf omU, proofOf tsPos, proofOf hNN, proofOf nlPos, proofOf rlTS
              , proofOf rlHt, proofOf rlNL, proofOf swTS, proofOf swHt, proofOf collTS
              ]

-- | OptMerge preserves enough leaves for IH.
--
-- >>> runTPWith cvc5 optMergeNumLeaves
-- Lemma: optMergeUnfold                          Q.E.D.
-- Lemma: treeSizePos                             Q.E.D.
-- Lemma: heightNonNeg                            Q.E.D.
-- Lemma: numLeavesPos                            Q.E.D.
-- Lemma: relabelNumLeaves                        Q.E.D.
-- Lemma: relabelHeight                           Q.E.D.
-- Lemma: swapNumLeaves                           Q.E.D.
-- Lemma: swapHeight                              Q.E.D.
-- Lemma: collapseNumLeaves                       Q.E.D.
-- Lemma: optMergeNumLeaves                       Q.E.D.
-- Functions proven terminating:
--   collapse, deepS, deepW, height, light2S, light2W, lightS, lightW, numLeaves, optMerge,
--   relabelFrom, sibS, sibW, swap, treeSize, treeWeight
-- [Proven] optMergeNumLeaves :: Ɐt ∷ HTree → Bool
optMergeNumLeaves :: TP (Proof (Forall "t" HTree -> SBool))
optMergeNumLeaves = do
   omU    <- recall optMergeUnfold
   tsPos  <- recall treeSizePos
   hNN    <- recall heightNonNeg
   nlPos  <- recall numLeavesPos
   rlNL   <- recall relabelNumLeaves
   rlHt   <- recall relabelHeight
   swNL   <- recall swapNumLeaves
   swHt   <- recall swapHeight
   collNL <- recall collapseNumLeaves

   lemma "optMergeNumLeaves"
       (\(Forall @"t" t) -> numLeaves t .>= 3 .=> numLeaves (optMerge t) .>= 2)
              [proofOf omU, proofOf tsPos, proofOf hNN, proofOf nlPos, proofOf rlNL,
        proofOf rlHt, proofOf swNL, proofOf swHt, proofOf collNL]

-- ** Optimality theorem

-- | Base case: optimality for a tree with exactly two leaves.
--
-- >>> runTPWith cvc5 optBase
-- [Proven] optBase :: Ɐwl ∷ Integer → Ɐsl ∷ Integer → Ɐwr ∷ Integer → Ɐsr ∷ Integer → Bool
optBase :: TP (Proof (Forall "wl" Integer -> Forall "sl" Integer -> Forall "wr" Integer -> Forall "sr" Integer -> SBool))
optBase = do
   loU <- recall leavesOfUnfold
   iaU <- recall insertAllUnfold
   siU <- recall sortedInsertUnfold
   bhU <- recall buildHuffmanUnfold

   calc "optBase"
       (\(Forall @"wl" wl) (Forall @"sl" sl) (Forall @"wr" wr) (Forall @"sr" sr) ->
           let t = sBin (sTip wl sl) (sTip wr sr)
           in cost (buildHuffman (leavesOf t)) .<= cost t) $
       \wl sl wr sr ->
           let t   = sBin (sTip wl sl) (sTip wr sr)
               wl0 = sTip wl 0
               wr0 = sTip wr 0
           in []
             |- cost (buildHuffman (leavesOf t))
             ?? loU `at` Inst @"t" t
             ?? loU `at` Inst @"t" (sTip wl sl)
             ?? loU `at` Inst @"t" (sTip wr sr)
             =: cost (buildHuffman (insertAll [wl0] [wr0]))
             ?? iaU `at` (Inst @"xs" [wl0], Inst @"ys" [wr0])
             =: cost (buildHuffman (sortedInsert wl0 [wr0]))
             ?? siU `at` (Inst @"t" wl0, Inst @"ts" [wr0])
             =: cases
                  [ wl .<= wr
                      ==> cost (buildHuffman [wl0, wr0])
                       ?? bhU `at` Inst @"ts" [wl0, wr0]
                       ?? siU `at` (Inst @"t" (sBin wl0 wr0), Inst @"ts" (nil :: SList HTree))
                       ?? bhU `at` Inst @"ts" [sBin wl0 wr0]
                       =: cost t
                       =: qed
                  , sNot (wl .<= wr)
                      ==> cost (buildHuffman [wr0, wl0])
                       ?? bhU `at` Inst @"ts" [wr0, wl0]
                       ?? siU `at` (Inst @"t" (sBin wr0 wl0), Inst @"ts" (nil :: SList HTree))
                       ?? bhU `at` Inst @"ts" [sBin wr0 wl0]
                       =: cost t
                       =: qed
                  ]

-- | Huffman optimality: for any tree @t@ with at least two leaves,
-- the Huffman tree built from @leavesOf t@ has cost at most @cost t@.
--
-- @numLeaves t >= 2 => cost (buildHuffman (leavesOf t)) <= cost t@
optimality :: TP (Proof (Forall "t" HTree -> SBool))
optimality = do
   tsPos <- recall treeSizePos
   nlPos <- recall numLeavesPos
   omU   <- recall optMergeUnfold
   omTS  <- recall optMergeTreeSize
   omNL  <- recall optMergeNumLeaves
   base  <- recall optBase

   sInduct "optimality"
       (\(Forall @"t" t) ->
           numLeaves t .>= 2 .=> cost (buildHuffman (leavesOf t)) .<= cost t)
       (treeSize, [proofOf tsPos]) $
       \ih t -> [numLeaves t .>= 2]
         |- cost (buildHuffman (leavesOf t)) .<= cost t
         =: [pCase| t of
               Tip{} -> trivial

               Bin l r -> cost (buildHuffman (leavesOf t)) .<= cost t
                       =: case l of
                            Tip{} -> case r of
                              Tip{} -> cost (buildHuffman (leavesOf t)) .<= cost t
                                    ?? base `at` (Inst @"wl" (sweight l), Inst @"sl" (ssymbol l),
                                                  Inst @"wr" (sweight r), Inst @"sr" (ssymbol r))
                                    =: sTrue
                                    =: qed

                              Bin{} -> cost (buildHuffman (leavesOf t)) .<= cost t
                                    ?? omU   `at` Inst @"t" t
                                    ?? omTS  `at` Inst @"t" t
                                    ?? omNL  `at` Inst @"t" t
                                    ?? tsPos `at` Inst @"t" t
                                    ?? nlPos `at` Inst @"t" l
                                    ?? nlPos `at` Inst @"t" r
                                    ?? ih    `at` Inst @"t" (optMerge t)
                                    ?? sorry
                                    =: sTrue
                                    =: qed

                            Bin{} -> cost (buildHuffman (leavesOf t)) .<= cost t
                                  ?? omU   `at` Inst @"t" t
                                  ?? omTS  `at` Inst @"t" t
                                  ?? omNL  `at` Inst @"t" t
                                  ?? tsPos `at` Inst @"t" t
                                  ?? nlPos `at` Inst @"t" l
                                  ?? nlPos `at` Inst @"t" r
                                  ?? ih    `at` Inst @"t" (optMerge t)
                                  ?? sorry
                                  =: sTrue
                                  =: qed
            |]
