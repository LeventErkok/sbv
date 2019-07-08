-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.Shannon
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves (instances of) Shannon's expansion theorem and other relevant
-- facts.  See: <http://en.wikipedia.org/wiki/Shannon's_expansion>
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Uninterpreted.Shannon where

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
pos f = f sTrue

-- | Negative Shannon cofactor of a boolean function, with
-- respect to its first argument
neg :: (SBool -> a) -> a
neg f = f sFalse

-----------------------------------------------------------------------------
-- * Shannon expansion theorem
-----------------------------------------------------------------------------

-- | Shannon's expansion over the first argument of a function. We have:
--
-- >>> shannon
-- Q.E.D.
shannon :: IO ThmResult
shannon = prove $ \x y z -> f x y z .== (x .&& pos f y z .|| sNot x .&& neg f y z)
 where f :: Ternary
       f = uninterpret "f"

-- | Alternative form of Shannon's expansion over the first argument of a function. We have:
--
-- >>> shannon2
-- Q.E.D.
shannon2 :: IO ThmResult
shannon2 = prove $ \x y z -> f x y z .== ((x .|| neg f y z) .&& (sNot x .|| pos f y z))
 where f :: Ternary
       f = uninterpret "f"

-----------------------------------------------------------------------------
-- * Derivatives
-----------------------------------------------------------------------------

-- | Computing the derivative of a boolean function (boolean difference).
-- Defined as exclusive-or of Shannon cofactors with respect to that
-- variable.
derivative :: Ternary -> Binary
derivative f y z = pos f y z .<+> neg f y z

-- | The no-wiggle theorem: If the derivative of a function with respect to
-- a variable is constant False, then that variable does not "wiggle" the
-- function; i.e., any changes to it won't affect the result of the function.
-- In fact, we have an equivalence: The variable only changes the
-- result of the function iff the derivative with respect to it is not False:
--
-- >>> noWiggle
-- Q.E.D.
noWiggle :: IO ThmResult
noWiggle = prove $ \y z -> sNot (f' y z) .<=> pos f y z .== neg f y z
  where f :: Ternary
        f  = uninterpret "f"
        f' = derivative f

-----------------------------------------------------------------------------
-- * Universal quantification
-----------------------------------------------------------------------------

-- | Universal quantification of a boolean function with respect to a variable.
-- Simply defined as the conjunction of the Shannon cofactors.
universal :: Ternary -> Binary
universal f y z = pos f y z .&& neg f y z

-- | Show that universal quantification is really meaningful: That is, if the universal
-- quantification with respect to a variable is True, then both cofactors are true for
-- those arguments. Of course, this is a trivial theorem if you think about it for a
-- moment, or you can just let SBV prove it for you:
--
-- >>> univOK
-- Q.E.D.
univOK :: IO ThmResult
univOK = prove $ \y z -> f' y z .=> pos f y z .&& neg f y z
  where f :: Ternary
        f  = uninterpret "f"
        f' = universal f

-----------------------------------------------------------------------------
-- * Existential quantification
-----------------------------------------------------------------------------

-- | Existential quantification of a boolean function with respect to a variable.
-- Simply defined as the conjunction of the Shannon cofactors.
existential :: Ternary -> Binary
existential f y z = pos f y z .|| neg f y z

-- | Show that existential quantification is really meaningful: That is, if the existential
-- quantification with respect to a variable is True, then one of the cofactors must be true for
-- those arguments. Again, this is a trivial theorem if you think about it for a moment, but
-- we will just let SBV prove it:
--
-- >>> existsOK
-- Q.E.D.
existsOK :: IO ThmResult
existsOK = prove $ \y z -> f' y z .=> pos f y z .|| neg f y z
  where f :: Ternary
        f  = uninterpret "f"
        f' = existential f
