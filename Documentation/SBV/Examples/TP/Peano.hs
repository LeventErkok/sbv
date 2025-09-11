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

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeAbstractions     #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeSynonymInstances #-}

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
         | Succ { prev :: Nat }

mkSymbolic ''Nat

-- | Numeric instance. Choices: We clamp everything at 'Zero'. Negation is identity.
instance Num Nat where
  fromInteger i | i <= 0 = Zero
                | True   = Succ (fromInteger (i - 1))

  a + Zero   = a
  a + Succ b = Succ (a + b)

  Zero   - _      = Zero
  Succ a - Zero   = Succ a
  Succ a - Succ b = a - b

  _ * Zero   = Zero
  a * Succ b = a + a * b

  abs = id

  signum Zero = 0
  signum _    = 1

  negate = id

-- Symbolic numeric instance, mirroring the above
instance Num SNat where
  fromInteger = literal . fromInteger

  (+) = plus
      where plus = smtFunction "sNatPlus" $
                     \a b -> [sCase|Nat a of
                               Zero   -> b
                               Succ p -> sSucc (p `plus` b)
                             |]

  (-) = subt
      where -- Quasi-quotes cannot be nested, so we have to have this explicit ite.
            subt = smtFunction "sNatSubtract" $
                     \a b -> ite (isZero a) sZero [sCase|Nat b of
                                                    Zero -> a
                                                    Succ p -> sprev a `subt` p
                                                  |]

  (*) = times
      where times = smtFunction "sNatTimes" $
                      \a b -> [sCase|Nat b of
                                Zero   -> sZero
                                Succ p -> a + a `times` p
                              |]

  abs = id

  signum a = [sCase|Nat a of
               Zero -> 0
               _    -> 1
             |]


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

-- | n2i is always non-negative
--
-- >>> runTP n2iNonNeg
-- Lemma: n2iNonNeg                        Q.E.D.
-- [Proven] n2iNonNeg :: Ɐn ∷ Nat → Bool
n2iNonNeg  :: TP (Proof (Forall "n" Nat -> SBool))
n2iNonNeg = inductNat "n2iNonNeg" (\(Forall n) -> n2i n .>= 0) []

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
                                  =: 1 + n2i (i2n i)
                                  ?? ih
                                  =: 1 + i
                                  =: qed

-- | Round trip from 'Nat' to 'Integer' and back:
--
-- >>> runTP n2i2n
-- Lemma: n2i2n                            Q.E.D.
-- [Proven] n2i2n :: Ɐn ∷ Nat → Bool
n2i2n :: TP (Proof (Forall "n" Nat -> SBool))
n2i2n = inductNat "n2i2n" (\(Forall n) -> i2n (n2i n) .== n) []


-- * Arithmetic

-- | Correctness of addition
--
-- >>> runTP addCorrect
addCorrect :: TP (Proof (Forall "n" Nat -> Forall "m" Nat -> SBool))
addCorrect = do
  let ih pf = axiom "inductNat" (sAnd [ quantifiedBool (\(Forall b)            -> pf sZero b)
                                      , quantifiedBool (\(Forall a) (Forall b) -> pf a b .=> pf (sSucc a) b)
                                      ]
                                 .=> quantifiedBool (\(Forall a) (Forall b) -> pf a b))

  let inductNat2 s p xs = do schema <- ih (\a b -> p (Forall a) (Forall b))
                             lemma s p (proofOf schema : xs)

  inductNat2 "addCorrect"
             (\(Forall n) (Forall m) -> n2i (n + m) .== n2i n + n2i m)
             []
