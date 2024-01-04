-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ProofTools.AddHorn
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example of invariant generation for a simple addition algorithm:
--
-- @
--    z = x
--    i = 0
--    assume y > 0
--
--    while (i < y)
--       z = z + 1
--       i = i + 1
--
--   assert z == x + y
-- @
--
-- We use the Horn solver to calculate the invariant and then show that it
-- indeed is a sufficient invariant to establish correctness.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ProofTools.AddHorn where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | Helper type synonym for the invariant.
type Inv = (SInteger, SInteger, SInteger, SInteger) -> SBool

-- | Helper type synonym for verification conditions.
type VC = Forall "x" Integer -> Forall "y" Integer -> Forall "z" Integer -> Forall "i" Integer -> SBool

-- | Helper for turning an invariant predicate to a boolean.
quantify :: Inv -> VC
quantify f = \(Forall x) (Forall y) (Forall z) (Forall i) -> f (x, y, z, i)

-- | First verification condition: Before the loop starts, invariant must hold:
--
-- \(z = x \land i = 0 \land y > 0 \Rightarrow inv (x, y, z, i)\)
vc1 :: Inv -> VC
vc1 inv = quantify $ \(x, y, z, i) -> z .== x .&& i .== 0 .&& y .> 0 .=> inv (x, y, z, i)

-- | Second verification condition: If the loop body executes, invariant must still hold at the end:
--
-- \(inv (x, y, z, i) \land i < y \Rightarrow inv (x, y, z+1, i+1)\)
vc2 :: Inv -> VC
vc2 inv = quantify $ \(x, y, z, i) -> inv (x, y, z, i) .&& i .< y .=> inv (x, y, z+1, i+1)

-- | Third verification condition: Once the loop exits, invariant and the negation of the loop condition
-- must establish the final assertion:
--
-- \(inv (x, y, z, i) \land i \geq y \Rightarrow z == x + y\)
vc3 :: Inv -> VC
vc3 inv = quantify $ \(x, y, z, i) -> inv (x, y, z, i) .&& i .>= y .=> z .== x + y

-- | Synthesize the invariant. We use an uninterpreted function for the SMT solver to synthesize. We get:
--
-- >>> synthesize
-- Satisfiable. Model:
--   invariant :: (Integer, Integer, Integer, Integer) -> Bool
--   invariant (x, y, z, i) = x + (-z) + i > (-1) && x + (-z) + i < 1 && x + y + (-z) > (-1)
--
-- This is a bit hard to read, but you can convince yourself it is equivalent to @x + i .== z .&& x + y .>= z@:
--
-- >>> let f (x, y, z, i) = x + (-z) + i .> (-1) .&& x + (-z) + i .< 1 .&& x + y + (-z) .> (-1)
-- >>> let g (x, y, z, i) = x + i .== z .&& x + y .>= z
-- >>> f === (g :: Inv)
-- Q.E.D.
synthesize :: IO SatResult
synthesize = sat vcs
  where invariant :: Inv
        invariant = uninterpretWithArgs "invariant" ["x", "y", "z", "i"]

        vcs :: ConstraintSet
        vcs = do setLogic $ CustomLogic "HORN"
                 constrain $ vc1 invariant
                 constrain $ vc2 invariant
                 constrain $ vc3 invariant

-- | Verify that the synthesized function does indeed work. To do so, we simply prove that the invariant found satisfies all the vcs:
--
-- >>> verify
-- Q.E.D.
verify :: IO ThmResult
verify = prove vcs
  where invariant :: Inv
        invariant (x, y, z, i) = x + (-z) + i .> (-1) .&& x + (-z) + i .< 1 .&& x + y + (-z) .> (-1)

        vcs :: SBool
        vcs =   quantifiedBool (vc1 invariant)
            .&& quantifiedBool (vc3 invariant)
            .&& quantifiedBool (vc3 invariant)

{- HLint ignore quantify "Redundant lambda" -}
