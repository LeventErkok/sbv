-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Misc.Enumerate
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates how enumerations can be translated to their SMT-Lib
-- counterparts, without losing any information content. Also see
-- "Data.SBV.Examples.Puzzles.U2Bridge" for a more detailed
-- example involving enumerations.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.Misc.Enumerate where

import Data.SBV
import Data.Generics

-- | A simple enumerated type, that we'd like to translate to SMT-Lib intact;
-- i.e., this type will not be uninterpreted but rather preserved and will
-- be just like any other symbolic type SBV provides. Note the automatically
-- derived slew of classes we need: 'Eq', 'Ord', 'Data', 'Typeable', 'Read',
-- and 'Show'. For symbolic enumerated types, you should
-- always let GHC derive these instances. Aside from these, we also need
-- instances for 'SymWord', 'HasKind' and 'SatModel'. Again, the default definitions suffice
-- so the actual declarations are straightforward.
--
-- Also note that we need to @import Data.Generics@ and have the @LANGUAGE@
-- option @DeriveDataTypeable@ set.
data E = A | B | C
       deriving (Eq, Ord, Data, Typeable, Read, Show)

-- | The 'SymWord' instance for 'E'. In GHC 7.10 and forward, we'll be able to add these to the @deriving@ clause as well.
instance SymWord E

-- | The 'HasKind' instance for 'E'. In GHC 7.10 and forward, we'll be able to add these to the @deriving@ clause as well.
instance HasKind E

-- | The 'SatModel' instance for 'E'. In GHC 7.10 and forward, we'll be able to add these to the @deriving@ clause as well.
-- Note that the 'SatModel' instance is only needed if you use 'getModel' and its friends; but it does not hurt to always
-- derive the default definitions.
instance SatModel E

-- | Give a name to the symbolic variants of 'E', for convenience
type SE = SBV E

-- | Have the SMT solver enumerate the elements of the domain. We have:
--
-- >>> elts
-- Solution #1:
--   s0 = A :: E
-- Solution #2:
--   s0 = B :: E
-- Solution #3:
--   s0 = C :: E
-- Found 3 different solutions.
elts :: IO AllSatResult
elts = allSat $ \(x::SE) -> x .== x

-- | Shows that if we require 4 distinct elements of the type 'E', we shall fail; as
-- the domain only has three elements. We have:
--
-- >>> four
-- Unsatisfiable
four :: IO SatResult
four = sat $ \a b c (d::SE) -> allDifferent [a, b, c, d]

-- | Enumerations are automatically ordered, so we can ask for the maximum
-- element. Note the use of quantification. We have:
--
-- >>> maxE
-- Satisfiable. Model:
--   maxE = C :: E
maxE :: IO SatResult
maxE = sat $ do mx <- exists "maxE"
                e  <- forall "e"
                return $ mx .>= (e::SE)

-- | Similarly, we get the minumum element. We have:
--
-- >>> minE
-- Satisfiable. Model:
--   minE = A :: E
minE :: IO SatResult
minE = sat $ do mx <- exists "minE"
                e  <- forall "e"
                return $ mx .<= (e::SE)
