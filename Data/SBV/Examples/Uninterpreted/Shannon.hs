-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Uninterpreted.Shannon
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Proves (instances of) Shannon's expansion theorem and other relevant
-- facts.  See: <http://en.wikipedia.org/wiki/Shannon's_expansion>
-----------------------------------------------------------------------------

module Data.SBV.Examples.Uninterpreted.Shannon where

import Data.SBV

-----------------------------------------------------------------------------
-- * Boolean functions
-----------------------------------------------------------------------------

-- | A ternary boolean function
type Ternary = SBool -> SBool -> SBool -> SBool

-- | A binary boolean function
type Binary = SBool -> SBool-> SBool

-----------------------------------------------------------------------------
-- * Shannon cofactors
-----------------------------------------------------------------------------

-- | Positive Shannon cofactor of a boolean function, with
-- respect to its first argument
pos :: (SBool -> a) -> a
pos f = f true

-- | Negative Shannon cofactor of a boolean function, with
-- respect to its first argument
neg :: (SBool -> a) -> a
neg f = f false

-----------------------------------------------------------------------------
-- * Shannon expansion theorem
-----------------------------------------------------------------------------

-- | Shannon's expansion over the first argument of a function. We have:
--
-- >>> shannon
-- Q.E.D.
shannon :: IO ThmResult
shannon = prove $ \x y z -> f x y z .== (x &&& pos f y z ||| bnot x &&& neg f y z)
 where f :: Ternary
       f = uninterpret "f"

-----------------------------------------------------------------------------
-- * Computing derivatives of boolean functions
-----------------------------------------------------------------------------

-- | Computing the derivative of a boolean function (boolean difference).
-- Defined as exclusive-or of Shannon cofactors with respect to that
-- variable.
derivative :: Ternary -> Binary
derivative f x y = f true x y <+> f false x y

-- | The no-wiggle theorem: If the derivative of a function with respect to
-- a variable is constant False, then that variable does not "wiggle" the
-- function; i.e., any changes to it won't affect the result of the function.
-- In fact, we have an equivalence: The variable only changes the
-- result of the function iff the derivative with respect to it is not False:
--
-- >>> noWiggle
-- Q.E.D.
noWiggle :: IO ThmResult
noWiggle = prove $ \y z -> bnot (f' y z) <=> f true y z .== f false y z
  where f :: Ternary
        f = uninterpret "f"
        f' = derivative f
