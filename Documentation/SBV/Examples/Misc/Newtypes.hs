-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Newtypes
-- Copyright : (c) Curran McConnell
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how to create symbolic newtypes with the same behaviour as
-- their wrapped type.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Documentation.SBV.Examples.Misc.Newtypes where

import Prelude hiding (ceiling)
import Data.SBV
import qualified Data.SBV.Internals as SI

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | A 'Metres' is a newtype wrapper around 'Integer'.
newtype Metres = Metres Integer deriving (Real, Integral, Num, Enum, Eq, Ord)

-- | Symbolic version of 'Metres'.
type SMetres   = SBV Metres

-- | To use 'Metres' symbolically, we associate it with the underlying symbolic
-- type's kind.
instance HasKind Metres where
   kindOf _ = KUnbounded

-- | The 'SymVal' instance simply uses stock definitions. This is always
-- possible for newtypes that simply wrap over an existing symbolic type.
instance SymVal Metres where
   mkSymVal = SI.genMkSymVar KUnbounded
   literal  = SI.genLiteral  KUnbounded
   fromCV   = SI.genFromCV

-- | Similarly, we can create another newtype, this time wrapping over 'Word16'. As an example,
-- consider measuring the human height in centimetres? The tallest person in history,
-- Robert Wadlow, was 272 cm. We don't need negative values, so 'Word16' is the smallest type that
-- suits our needs.
newtype HumanHeightInCm = HumanHeightInCm Word16 deriving (Real, Integral, Num, Enum, Eq, Ord)

-- | Symbolic version of 'HumanHeightInCm'.
type SHumanHeightInCm = SBV HumanHeightInCm

-- | Symbolic instance simply follows the underlying type, just like 'Metres'.
instance HasKind HumanHeightInCm where
    kindOf _ = KBounded False 16

-- | Similarly here, for the 'SymVal' instance.
instance SymVal HumanHeightInCm where
    mkSymVal = SI.genMkSymVar $ KBounded False 16
    literal  = SI.genLiteral  $ KBounded False 16
    fromCV   = SI.genFromCV

-- | The tallest human ever was 272 cm. We can simply use 'literal' to lift it
-- to the symbolic space.
tallestHumanEver :: SHumanHeightInCm
tallestHumanEver = literal 272

-- | Given a distance between a floor and a ceiling, we can see whether
-- the human can stand in that room. Comparison is expressed using 'sFromIntegral'.
ceilingHighEnoughForHuman :: SMetres -> SHumanHeightInCm -> SBool
ceilingHighEnoughForHuman ceiling humanHeight = humanHeight' .< ceiling'
    where -- In a real codebase, the code for comparing these newtypes
          -- should be reusable, perhaps through a typeclass.
        ceiling'     = literal 100 * sFromIntegral ceiling :: SInteger
        humanHeight' = sFromIntegral humanHeight :: SInteger

-- | Now, suppose we want to see whether we could design a room with a ceiling
-- high enough that any human could stand in it. We have:
--
-- >>> sat problem
-- Satisfiable. Model:
--   floorToCeiling =   3 :: Integer
--   humanheight    = 272 :: Word16
problem :: Predicate
problem = do
    ceiling     :: SMetres          <- free "floorToCeiling"
    humanHeight :: SHumanHeightInCm <- free "humanheight"
    constrain $ humanHeight .== tallestHumanEver

    return $ ceilingHighEnoughForHuman ceiling humanHeight
