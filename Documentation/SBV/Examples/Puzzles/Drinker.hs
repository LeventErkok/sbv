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

-- | Formulate the drinkers paradox, if some one is drinking, then everyone is!
--
-- >>> drinker
-- Q.E.D.
drinker :: IO ThmResult
drinker = prove $ \(Exists x) (Forall y) -> d x .=> d y
