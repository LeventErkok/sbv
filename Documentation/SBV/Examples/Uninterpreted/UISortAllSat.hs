-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.UISortAllSat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates uninterpreted sorts and how all-sat behaves for them.
-- Thanks to Eric Seidel for the idea.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Uninterpreted.UISortAllSat where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | A "list-like" data type, but one we plan to uninterpret at the SMT level.
-- The actual shape is really immaterial for us.
data L

-- | Make 'L' into an uninterpreted sort, automatically introducing 'SL'
-- as a synonym for 'SBV' 'L'.
mkUninterpretedSort ''L

-- | An uninterpreted "classify" function. Really, we only care about
-- the fact that such a function exists, not what it does.
classify :: SL -> SInteger
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
-- >>> allSat genLs
-- Solution #1:
--   l  = L!val!2 :: L
--   l0 = L!val!0 :: L
--   l1 = L!val!1 :: L
--   l2 = L!val!2 :: L
-- <BLANKLINE>
--   classify :: L -> Integer
--   classify L!val!2 = 2
--   classify L!val!1 = 1
--   classify _       = 0
-- Solution #2:
--   l  = L!val!1 :: L
--   l0 = L!val!0 :: L
--   l1 = L!val!1 :: L
--   l2 = L!val!2 :: L
-- <BLANKLINE>
--   classify :: L -> Integer
--   classify L!val!2 = 2
--   classify L!val!1 = 1
--   classify _       = 0
-- Solution #3:
--   l  = L!val!0 :: L
--   l0 = L!val!0 :: L
--   l1 = L!val!1 :: L
--   l2 = L!val!2 :: L
-- <BLANKLINE>
--   classify :: L -> Integer
--   classify L!val!2 = 2
--   classify L!val!1 = 1
--   classify _       = 0
-- Found 3 different solutions.
genLs :: Predicate
genLs = do [l, l0, l1, l2] <- symbolics ["l", "l0", "l1", "l2"]
           constrain $ classify l0 .== 0
           constrain $ classify l1 .== 1
           constrain $ classify l2 .== 2
           return $ l .== l0 .|| l .== l1 .|| l .== l2
