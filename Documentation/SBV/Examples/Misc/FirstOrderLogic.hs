-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.FirstOrderLogic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves various first-order logic properties using SBV. The properties we
-- prove all come from <https://en.wikipedia.org/wiki/First-order_logic>
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.FirstOrderLogic where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only, ignore.
-- >>> import Data.SBV

-- | An uninterpreted sort for demo purposes, named 'U'
data U
mkUninterpretedSort ''U

-- | An uninterpreted sort for demo purposes, named 'V'
data V
mkUninterpretedSort ''V

-- | Helper to turn quantified formula to a regular boolean. We
-- can think of this as quantifier elimination, hence the name 'qe'.
qe :: QuantifiedBool a => a -> SBool
qe = quantifiedBool

-- * Pushing negation over quantifiers
{- $negUniv
\(\lnot \forall x\,P(x)\Leftrightarrow \exists x\,\lnot P(x)\)

>>> let p = uninterpret "p" :: SU -> SBool
>>> prove $ sNot (qe (\(Forall x) -> p x)) .<=> qe (\(Exists x) -> sNot (p x))
Q.E.D.

\(\lnot \exists x\,P(x)\Leftrightarrow \forall x\,\lnot P(x)\)

>>> let p = uninterpret "p" :: SU -> SBool
>>> prove $ sNot (qe (\(Exists x) -> p x)) .<=> qe (\(Forall x) -> sNot (p x))
Q.E.D.
-}

-- * Interchanging quantifiers
{- $interchange
\(\forall x\,\forall y\,P(x,y)\Leftrightarrow \forall y\,\forall x\,P(x,y)\)

>>> let p = uninterpret "p" :: (SU, SV) -> SBool
>>> prove $ qe (\(Forall x) (Forall y) -> p (x, y)) .<=> qe (\(Forall y) (Forall x) -> p (x, y))
Q.E.D.

\(\exists x\,\exists y\,P(x,y)\Leftrightarrow \exists y\,\exists x\,P(x,y)\)

>>> let p = uninterpret "p" :: (SU, SV) -> SBool
>>> prove $ qe (\(Exists x) (Exists y) -> p (x, y)) .<=> qe (\(Exists y) (Exists x) -> p (x, y))
Q.E.D.
-}
