-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Coins
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving the classic coin change theorem: For any amount @n >= 8@, you can make
-- exact change using only 3-cent and 5-cent coins.
--
-- This example is inspired by: <https://github.com/imandra-ai/imandrax-examples/blob/main/src/coins.iml>
-----------------------------------------------------------------------------

{-# LANGUAGE CPP               #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Coins where

import Data.SBV
import Data.SBV.Maybe hiding (maybe)
import qualified Data.SBV.Maybe as SM
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Types

-- | A pocket contains a count of 3-cent and 5-cent coins.
data Pocket = Pocket { num3s :: Integer
                     , num5s :: Integer
                     }

-- | Create a symbolic version of Pocket.
mkSymbolic [''Pocket]

-- * Making change

-- | Make change for a given amount. Returns 'Nothing' if the amount is less than 8.
-- Base cases:
--
--   * 8 = 3 + 5
--   * 9 = 3 + 3 + 3
--   * 10 = 5 + 5
--
-- For @n > 10@, we use change for @n-3@ and add one more 3-cent coin.
mkChange :: SInteger -> SMaybe Pocket
mkChange = smtFunction "mkChange" $ \n ->
    ite (n .< 8)  sNothing
  $ ite (n .== 8) (sJust (sPocket 1 1))
  $ ite (n .== 9) (sJust (sPocket 3 0))
  $ ite (n .== 10) (sJust (sPocket 0 2))
  -- n > 10: use change for (n-3) and add a 3-cent coin
  $ [sCase|Pocket fromJust (mkChange (n - 3)) of
       Pocket n3 n5 -> sJust (sPocket (n3 + 1) n5)
    |]

-- | Evaluate the value of a pocket (total cents).
evalPocket :: SMaybe Pocket -> SInteger
evalPocket mp = SM.maybe 0 (\p -> 3 * snum3s p + 5 * snum5s p) mp

-- * Correctness

-- | Prove that for any @n >= 8@, @mkChange@ produces a pocket that evaluates to @n@.
--
-- We have:
--
-- >>> runTP correctness
-- Inductive lemma (strong): mkChangeCorrect
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (5 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.4                           Q.E.D.
--     Step: 1.5.1                         Q.E.D.
--     Step: 1.5.2                         Q.E.D.
--     Step: 1.5.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mkChangeCorrect :: Ɐn ∷ Integer → Bool
correctness :: TP (Proof (Forall "n" Integer -> SBool))
correctness = do
    sInduct "mkChangeCorrect"
            (\(Forall n) -> n .>= 8 .=> evalPocket (mkChange n) .== n)
            (\n -> n, []) $
            \ih n -> [n .>= 8]
                  |- evalPocket (mkChange n) .== n
                  =: cases [ n .== 8  ==> trivial
                           , n .== 9  ==> trivial
                           , n .== 10 ==> trivial
                           , n .< 8   ==> trivial   -- Vacuously true: contradicts n >= 8
                           , n .> 10  ==> evalPocket (mkChange n) .== n
                                       =: [sCase|Pocket fromJust (mkChange (n - 3)) of
                                            Pocket n3 n5 -> evalPocket (sJust (sPocket (n3 + 1) n5)) .== n
                                         |]
                                       ?? ih `at` Inst @"n" (n - 3)
                                       =: sTrue
                                       =: qed
                           ]
