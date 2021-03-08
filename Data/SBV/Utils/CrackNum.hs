-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.CrackNum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Crack internal representation for numeric types
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Utils.CrackNum (
        crackNum
      ) where

import Data.SBV.Core.Concrete
import Data.SBV.Core.Kind
import Data.SBV.Core.SizedFloats
import Data.SBV.Utils.Numeric

import LibBF

-- | A class for cracking things deeper, if we know how.
class CrackNum a where
  crackNum :: a -> Maybe String

instance CrackNum CV where
  crackNum cv = case kindOf cv of
                  -- Maybe one day we'll have a use for these, currently cracking them
                  -- any further seems overkill
                  KBool      {}  -> Nothing
                  KUnbounded {}  -> Nothing
                  KReal      {}  -> Nothing
                  KUserSort  {}  -> Nothing
                  KChar      {}  -> Nothing
                  KString    {}  -> Nothing
                  KList      {}  -> Nothing
                  KSet       {}  -> Nothing
                  KTuple     {}  -> Nothing
                  KMaybe     {}  -> Nothing
                  KEither    {}  -> Nothing

                  -- Actual crackables
                  KFloat{}       -> Just $ let CFloat   f     = cvVal cv in float  8 24 (fromIntegral (floatToWord f))
                  KDouble{}      -> Just $ let CDouble  d     = cvVal cv in float 11 53 (fromIntegral (doubleToWord d))
                  KFP eb sb      -> Just $ let CFP (FP _ _ f) = cvVal cv in float eb sb (bfToBits (mkBFOpts eb sb NearEven) f)
                  KBounded sg sz -> Just $ let CInteger i     = cvVal cv in int   sg sz i

-- | Show a sized word/int in detail
int :: Bool -> Int -> Integer -> String
int _signed _sz _v = ""

-- | Show a float in detail
float :: Int -> Int -> Integer -> String
float _eb _sz _v = ""
