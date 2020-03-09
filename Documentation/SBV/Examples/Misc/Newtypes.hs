-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Newtypes
-- Copyright : (c) Levent Erkok
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

-- | This first type we will construct for our example is `Metres`, wrapping `Integer`.
newtype Metres = Metres Integer deriving (Real, Integral, Num, Enum, Eq, Ord)
type SMetres   = SBV Metres

-- | So we consult the instance for 'HasKind Integer' and write the same instance.
instance HasKind Metres where
   kindOf _ = KUnbounded

-- | And we feed the 'Kind' of 'Metres', i.e., 'KUnbounded' into some functions from
-- 'Data.SBV.Internals' in order to create a 'SymVal Metres' instance.
instance SymVal Metres where
   mkSymVal = SI.genMkSymVar KUnbounded
   literal  = SI.genLiteral  KUnbounded
   fromCV   = SI.genFromCV

-- | Now, what if we want to measure human height in centimetres? The tallest person in history,
-- Robert Wadlow, was 272 cm. We don't need negative values, so 'Word16' is the smallest type that
-- suits our needs.
newtype HumanHeightInCm = HumanHeightInCm Word16 deriving (Real, Integral, Num, Enum, Eq, Ord)
type SHumanHeightInCm = SBV HumanHeightInCm

-- | So again we consult the 'HasKind Word16' instance to write the instance for 'HumanHeightInCm'.
instance HasKind HumanHeightInCm where
    kindOf _ = KBounded False 16

-- | And we do the same for 'SymVal'.
instance SymVal HumanHeightInCm where
    mkSymVal = SI.genMkSymVar $ KBounded False 16
    literal  = SI.genLiteral  $ KBounded False 16
    fromCV   = SI.genFromCV

-- | The tallest human ever was 272 cm.
tallestHumanEver :: SHumanHeightInCm
tallestHumanEver = literal 272

-- | Given a distance between a floor and a ceiling, we can see whether
-- the human can stand in that room. We can express the comparison using
-- 'sFromIntegral'.
ceilingHighEnoughForHuman :: SMetres -> SHumanHeightInCm -> SBool
ceilingHighEnoughForHuman ceiling humanHeight = humanHeight' .< ceiling'
    where
        -- In a real codebase, the code for comparing these newtypes
        -- should be reusable, perhaps through a typeclass.
        ceiling'     = (literal 100) * sFromIntegral ceiling :: SInteger
        humanHeight' = sFromIntegral humanHeight :: SInteger

-- | Now, suppose we want to see whether we could design a room with a ceiling
-- high enough that any human could stand in it.
problem :: Predicate
problem = do
    ceiling     :: SMetres          <- free "floorToCeiling"
    humanHeight :: SHumanHeightInCm <- free "humanheight"
    constrain $ humanHeight .<= tallestHumanEver
    return $ ceilingHighEnoughForHuman ceiling humanHeight

-- | This is easily satisfiable.
isThereAValidCeilingHeight :: IO ()
isThereAValidCeilingHeight = print =<< sat problem
