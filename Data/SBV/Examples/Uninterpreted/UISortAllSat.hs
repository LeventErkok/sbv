-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Uninterpreted.UISortAllSat
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates uninterpreted sorts and how all-sat behaves for them.
-- Thanks to Eric Seidel for the idea.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}

module Data.SBV.Examples.Uninterpreted.UISortAllSat where

import Data.Generics
import Data.SBV

-- | A "list-like" data type, but one we plan to uninterpret at the SMT level.
-- The actual shape is really immaterial for us, but could be used as a proxy
-- to generate test cases or explore data-space in some other part of a program.
-- Note that we neither rely on the shape of this data, nor need the actual
-- constructors.
data L = Nil
       | Cons Int L
       deriving (Eq, Ord, Data, Typeable, Read, Show)

-- | Declare instances to make 'L' a usable uninterpreted sort. First we need the
-- 'SymWord' instance, with the default definition sufficing.
instance SymWord L

-- | Similarly, 'HasKind's default implementation is sufficient.
instance HasKind L

-- | An uninterpreted "classify" function. Really, we only care about
-- the fact that such a function exists, not what it does.
classify :: SBV L -> SInteger
classify = uninterpret "classify"

-- | Formulate a query that essentially asserts a cardinality constraint on
-- the uninterpreted sort 'L'. The goal is to say there are precisely 3
-- such things, as it might be the case. We manage this by declaring four
-- elements, and asserting that for a free variable of this sort, the
-- shape of the data matches one of these three instances. That is, we
-- assert that all the instances of the data 'L' can be classified into
-- 3 equivalence classes. Then, allSat returns all the possible instances,
-- which of course are all uninterpreted.
--
-- As expected, we have:
--
-- >>> genLs
-- Solution #1:
--   l = L!val!0 :: L
--   l0 = L!val!0 :: L
--   l1 = L!val!1 :: L
--   l2 = L!val!2 :: L
-- Solution #2:
--   l = L!val!2 :: L
--   l0 = L!val!0 :: L
--   l1 = L!val!1 :: L
--   l2 = L!val!2 :: L
-- Solution #3:
--   l = L!val!1 :: L
--   l0 = L!val!0 :: L
--   l1 = L!val!1 :: L
--   l2 = L!val!2 :: L
-- Found 3 different solutions.
genLs :: IO AllSatResult
genLs = allSatWith z3
               $ do [l, l0, l1, l2] <- symbolics ["l", "l0", "l1", "l2"]
                    constrain $ classify l0 .== 0
                    constrain $ classify l1 .== 1
                    constrain $ classify l2 .== 2
                    return $ l .== l0 ||| l .== l1 ||| l .== l2
