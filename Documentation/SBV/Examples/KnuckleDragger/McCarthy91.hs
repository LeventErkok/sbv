-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.McCarthy91
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving McCarthy's 91 function correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.McCarthy91 where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- * Definitions

-- | Nested recursive definition of McCarthy's function.
mcCarthy91 :: SInteger -> SInteger
mcCarthy91 = smtFunction "mcCarthy91" $ \n -> ite (n .> 100)
                                                  (n - 10)
                                                  (mcCarthy91 (mcCarthy91 (n + 11)))
-- | Specification for McCarthy's function.
spec91 :: SInteger -> SInteger
spec91 n = ite (n .> 100) (n - 10) 91

-- * Correctness

-- | We prove the equivalence of the nested recursive definition against the spec with a case analysis
-- and strong induction. We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

   -- We start by establishing that @n < mcCarthy91 n + 11@. This will come in handy when we do the induction later.
   -- https://github.com/acl2/acl2/blob/be39e7835f1c68008c17188d2f65eeaef61632fa/books/workshops/2000/ruiz/multiset/examples/mccarthy-91/mccarthy-91.lisp#L4
   smaller <- lemma "smaller"
                     (\(Forall @"n" n) -> n .< mcCarthy91 n + 11)
                     [sorry]

   -- Case 1. When @n > 100@
   case1 <- lemma "case1" (\(Forall @"n" n) -> n .>= 100 .=> mcCarthy91 n .== spec91 n) []

   -- Case 2. When @90 <= n <= 100@
   case2 <- lemma "case2" (\(Forall @"n" n) -> 90 .<= n .&& n .<= 100 .=> mcCarthy91 n .== spec91 n) []

   -- Case 3. When @n < 90@
   case3 <- sInduct "case3"
                    (\(Forall @"n" n) -> n .< 90 .=> mcCarthy91 n .== spec91 n)
                    (\(n :: SInteger) -> 101 - n) $
                    \ih n -> [n .< 90] |- mcCarthy91 n
                                       ?? "unfold"
                                       =: mcCarthy91 (mcCarthy91 (n + 11))
                                       ?? [ smaller `at` Inst @"n" (mcCarthy91 (n + 11))
                                          , ih      `at` Inst @"n" (n + 11)
                                          ]
                                       =: spec91 (n + 11)
                                       =: qed

   -- Putting it all together
   calc "mcCarthy91"
        (\(Forall @"n" n) -> mcCarthy91 n .== spec91 n) $
        \n -> [] |- cases [ n .> 100               ==> mcCarthy91 n ?? case1 =: spec91 n =: qed
                          , 90 .<= n .&& n .<= 100 ==> mcCarthy91 n ?? case2 =: spec91 n =: qed
                          , n .< 90                ==> mcCarthy91 n ?? case3 =: spec91 n =: qed
                          ]
