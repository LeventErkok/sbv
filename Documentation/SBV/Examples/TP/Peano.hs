-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Peano
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some basic TP usage.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP             #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Peano where

import Data.SBV
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Natural numbers
data Nat = Zero
         | Succ Nat

mkSymbolic ''Nat

-- * Conversion to and from integers

-- | Convert from 'Nat' to 'Integer':
n2i :: SNat -> SInteger
n2i = smtFunction "n2i" $ \n -> [sCase|Nat n of
                                   Zero   -> 0
                                   Succ p -> 1 + n2i p
                                |]

-- | Convert Non-negative integers to 'Nat'. Negative numbers become 'Zero'.
i2n :: SInteger -> SNat
i2n = smtFunction "i2n" $ \i -> ite (i .<= 0) sZero (sSucc (i2n (i - 1)))

-- | Round trip from 'Integer' to 'Nat' and back:
--
-- >>> runTP i2n2i
-- Inductive lemma: i2n2i
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] i2n2i :: Ɐi ∷ Integer → Bool
i2n2i :: TP (Proof (Forall "i" Integer -> SBool))
i2n2i = induct "i2n2i"
               (\(Forall i) -> i .>= 0 .=> n2i (i2n i) .== i) $
               \ih i -> [i .>= 0] |- n2i (i2n (i+1))
                                  =: n2i (sSucc (i2n i))
                                  =: 1+n2i (i2n i)
                                  ?? ih
                                  =: 1+i
                                  =: qed

-- | Round trip from 'Nat' to 'Integer' and back:
--
n2i2n :: TP (Proof (Forall "n" Nat -> SBool))
n2i2n = lemma "n2i2n" (\(Forall n) -> i2n (n2i n) .== n) []
