-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.DeltaSat.DeltaSat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The encoding of the Flyspec example from the dReal web page
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.DeltaSat.DeltaSat where

import Data.SBV

-- | Encode the delta-sat problem as given in <http://dreal.github.io/>
-- We have:
--
-- >>> flyspeck
-- Unsatisfiable
flyspeck :: IO SatResult
flyspeck = dsat $ do
        x1 <- sReal "x1"
        x2 <- sReal "x2"

        constrain $ x1 `inRange` ( 3, 3.14)
        constrain $ x2 `inRange` (-7, 5)

        let pi' = 3.14159265
            lhs = 2 * pi' - 2 * x1 * asin (cos 0.979 * sin (pi' / x1))
            rhs = -0.591 - 0.0331 * x2 + 0.506 + 1

        pure $ lhs .<= rhs
