-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Drinker
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- SBV proof of the drinker paradox: <http://en.wikipedia.org/wiki/Drinker_paradox>
--
-- Let P be the non-empty set of people in a bar. The theorem says if there is somebody drinking in the bar,
-- then everybody is drinking in the bar. The general formulation is:
--
-- @
--     ∃x : P. D(x) -> ∀y : P. D(y)
-- @
--
-- In SBV, quantifiers are allowed, but you need to put the formula into prenex normal form manually. See
-- <http://en.wikipedia.org/wiki/Prenex_normal_form> for details. (Note that you do not need to do skolemization
-- by hand, though SBV will do that for you automatically as well as it casts the problem into an SMT query.)
-- If we transform the above to prenex form, we get:
--
-- @
--     ∃x : P. ∀y : P. D(x) -> D(y)
-- @
--
-- In this file, we show two different ways of proving the above in SBV; one using the monadic style,
-- and the other using the expression style.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Drinker where

import Data.SBV

-- | Declare a carrier data-type in Haskell named P, representing all the people in a bar.
data P

-- | Make 'P' an uninterpreted sort, introducing the type 'SP' for its symbolic version
mkUninterpretedSort ''P

-- | Declare the uninterpret function 'd', standing for drinking. For each person, this function
-- assigns whether they are drinking; but is otherwise completely uninterpreted. (i.e., our theorem
-- will be true for all such functions.)
d :: SP -> SBool
d = uninterpret "D"

-- | Monadic formulation. In this style, we use the 'sbvExists' and 'sbvForall' constructs to create
-- our quantified variables. We have:
--
-- >>> drinker1
-- Q.E.D.
drinker1 :: IO ThmResult
drinker1 = prove $ do x <- sbvExists "x"
                      y <- sbvForall "y"

                      pure $ d x .=> d y

-- | Expression level formulation. In this style, we use the 'existential' and 'universal' functions instead.
-- We have:
--
-- >>> drinker2
-- Q.E.D.
drinker2 :: IO ThmResult
drinker2 = prove $ existential ["x"] $ \x ->
                     universal ["y"] $ \y ->
                        d x .=> d y
