-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Enumerate
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how enumerations can be translated to their SMT-Lib
-- counterparts, without losing any information content. Also see
-- "Documentation.SBV.Examples.Puzzles.U2Bridge" for a more detailed
-- example involving enumerations.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Enumerate where

import Data.SBV

-- | A simple enumerated type, that we'd like to translate to SMT-Lib intact;
-- i.e., this type will not be uninterpreted but rather preserved and will
-- be just like any other symbolic type SBV provides.
--
-- Also note that we need to have the following @LANGUAGE@ options defined:
-- @TemplateHaskell@, @StandaloneDeriving@, @DeriveDataTypeable@, @DeriveAnyClass@ for
-- this to work.
data E = A | B | C

-- | Make 'E' a symbolic value.
mkSymbolicEnumeration ''E

-- | Have the SMT solver enumerate the elements of the domain. We have:
--
-- >>> elts
-- Solution #1:
--   s0 = C :: E
-- Solution #2:
--   s0 = B :: E
-- Solution #3:
--   s0 = A :: E
-- Found 3 different solutions.
elts :: IO AllSatResult
elts = allSat $ \(x::SE) -> x .== x

-- | Shows that if we require 4 distinct elements of the type 'E', we shall fail; as
-- the domain only has three elements. We have:
--
-- >>> four
-- Unsatisfiable
four :: IO SatResult
four = sat $ \a b c (d::SE) -> distinct [a, b, c, d]

-- | Enumerations are automatically ordered, so we can ask for the maximum
-- element. Note the use of quantification. We have:
--
-- >>> maxE
-- Satisfiable. Model:
--   maxE = C :: E
maxE :: IO SatResult
maxE = sat $ do mx :: SE <- free "maxE"
                constrain $ \(Forall e) -> mx .>= e

-- | Similarly, we get the minimum element. We have:
--
-- >>> minE
-- Satisfiable. Model:
--   minE = A :: E
minE :: IO SatResult
minE = sat $ do mn :: SE <- free "minE"
                constrain $ \(Forall e) -> mn .<= e
