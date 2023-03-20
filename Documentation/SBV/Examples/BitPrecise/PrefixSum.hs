-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.BitPrecise.PrefixSum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The PrefixSum algorithm over power-lists and proof of
-- the Ladner-Fischer implementation.
-- See <http://dl.acm.org/citation.cfm?id=197356>
-- and <http://www.cs.utexas.edu/~plaxton/c/337/05f/slides/ParallelRecursion-4.pdf>.
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.BitPrecise.PrefixSum where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

----------------------------------------------------------------------
-- * Formalizing power-lists
----------------------------------------------------------------------

-- | A poor man's representation of powerlists and
-- basic operations on them: <http://dl.acm.org/citation.cfm?id=197356>
-- We merely represent power-lists by ordinary lists.
type PowerList a = [a]

-- | The tie operator, concatenation.
tiePL :: PowerList a -> PowerList a -> PowerList a
tiePL = (++)

-- | The zip operator, zips the power-lists of the same size, returns
-- a powerlist of double the size.
zipPL :: PowerList a -> PowerList a -> PowerList a
zipPL []     []     = []
zipPL (x:xs) (y:ys) = x : y : zipPL xs ys
zipPL _      _      = error "zipPL: nonsimilar powerlists received"

-- | Inverse of zipping.
unzipPL :: PowerList a -> (PowerList a, PowerList a)
unzipPL = unzip . chunk2
  where chunk2 []       = []
        chunk2 (x:y:xs) = (x,y) : chunk2 xs
        chunk2 _        = error "unzipPL: malformed powerlist"

----------------------------------------------------------------------
-- * Reference prefix-sum implementation
----------------------------------------------------------------------

-- | Reference prefix sum (@ps@) is simply Haskell's @scanl1@ function.
ps :: (a, a -> a -> a) -> PowerList a -> PowerList a
ps (_, f) = scanl1 f

----------------------------------------------------------------------
-- * The Ladner-Fischer parallel version
----------------------------------------------------------------------

-- | The Ladner-Fischer (@lf@) implementation of prefix-sum. See <http://www.cs.utexas.edu/~plaxton/c/337/05f/slides/ParallelRecursion-4.pdf>
-- or pg. 16 of <http://dl.acm.org/citation.cfm?id=197356>
lf :: (a, a -> a -> a) -> PowerList a -> PowerList a
lf _ []         = error "lf: malformed (empty) powerlist"
lf _ [x]        = [x]
lf (zero, f) pl = zipPL (zipWith f (rsh lfpq) p) lfpq
   where (p, q) = unzipPL pl
         pq     = zipWith f p q
         lfpq   = lf (zero, f) pq
         rsh xs = zero : init xs


----------------------------------------------------------------------
-- * Sample proofs for concrete operators
----------------------------------------------------------------------

-- | Correctness theorem, for a powerlist of given size, an associative operator, and its left-unit element.
flIsCorrect :: Int -> (forall a. (OrdSymbolic a, Num a, Bits a) => (a, a -> a -> a)) -> Symbolic SBool
flIsCorrect n zf = do
        args :: PowerList SWord32 <- mkFreeVars n
        return $ ps zf args .== lf zf args

-- | Proves Ladner-Fischer is equivalent to reference specification for addition.
-- @0@ is the left-unit element, and we use a power-list of size @8@. We have:
--
-- >>> thm1
-- Q.E.D.
thm1 :: IO ThmResult
thm1 = prove $ flIsCorrect  8 (0, (+))

-- | Proves Ladner-Fischer is equivalent to reference specification for the function @max@.
-- @0@ is the left-unit element, and we use a power-list of size @16@. We have:
--
-- >>> thm2
-- Q.E.D.
thm2 :: IO ThmResult
thm2 = prove $ flIsCorrect 16 (0, smax)
