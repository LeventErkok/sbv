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

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Peano where

import Data.SBV
import Data.SBV.TP

import Data.SBV.Internals hiding (free)
import Data.Proxy
import GHC.TypeLits (KnownSymbol, symbolVal)

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

instance KnownSymbol n => Inductive (Forall n Nat -> SBool) where
  type IHType (Forall n Nat -> SBool) = SBool
  type IHArg  (Forall n Nat -> SBool) = SNat

  inductionStrategy result steps = do
     let nn = symbolVal (Proxy @n)
     n  <- free nn

     let bc = result (Forall sZero)
         ih = internalAxiom "IH" (result (Forall n))

     mkIndStrategy Nothing
                   (Just bc)
                   (steps ih n)
                   (observeIf not  ("P(" ++ nn ++ ")") (result (Forall (sSucc n))))
                   (\checkedLabel -> free nn >>= qcRun checkedLabel . steps ih)


-- | n2i is always non-negative
--
-- >>> runTP n2iNonNeg
-- Inductive lemma: n2iNonNeg
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] n2iNonNeg :: Ɐn ∷ Nat → Bool
n2iNonNeg  :: TP (Proof (Forall "n" Nat -> SBool))
n2iNonNeg = induct "n2iNonNeg"
                    (\(Forall n) -> n2i n .>= 0) $
                    \ih n -> [] |- n2i (sSucc n) .>= 0
                                =: 1 + n2i n .>= 0
                                ?? ih
                                =: sTrue
                                =: qed

-- | Round trip from 'Nat' to 'Integer' and back:
--
-- >>> runTP n2i2n
-- Lemma: n2iNonNeg                        Q.E.D.
-- Inductive lemma: n2i2n
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] n2i2n :: Ɐn ∷ Nat → Bool
n2i2n :: TP (Proof (Forall "n" Nat -> SBool))
n2i2n = do n2iNN <- recall "n2iNonNeg" n2iNonNeg
           induct "n2i2n"
                  (\(Forall n) -> i2n (n2i n) .== n) $
                  \ih n -> [] |- i2n (n2i (sSucc n))
                              =: i2n (1 + n2i n)
                              ?? n2iNN
                              =: sSucc (i2n (n2i n))
                              ?? ih
                              =: sSucc n
                              =: qed
