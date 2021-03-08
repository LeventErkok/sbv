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

import Data.Bits
import Data.List

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

-- How far off the screen we want displayed? Somewhat experimentally found.
tab :: String
tab = replicate 18 ' '

-- | Show a sized word/int in detail
int :: Bool -> Int -> Integer -> String
int _signed sz v = intercalate "\n" $ ruler ++ info
  where intSplits i sofar
          | i == 0 = sofar
          | i < 4  = i : sofar
          | True   = intSplits (i-4) (4 : sofar)

        splits = intSplits sz []

        ruler = map (tab ++) $ mkRuler sz splits

        info = ["          Binary: " ++ space splits [if v `testBit` i then '1' else '0' | i <- reverse [0 .. sz - 1]]]

-- | Show a float in detail
float :: Int -> Int -> Integer -> String
float eb sb v = intercalate "\n" $ ruler ++ legend : info
   where splits = [1, eb, sb]
         ruler  = map (tab ++) $ mkRuler (eb + sb) splits

         legend = tab ++ "S " ++ mkTag ('E' : show eb) eb ++ " " ++ mkTag ('F' : show (sb-1)) (sb-1)

         mkTag t len = take len $ replicate ((len - length t) `div` 2) '-' ++ t ++ repeat '-'

         info = ["          Binary: " ++ space splits [if v `testBit` i then '1' else '0' | i <- reverse [0 .. eb + sb - 1]]]


-- | Build a ruler with given split points
mkRuler :: Int -> [Int] -> [String]
mkRuler n splits = map (space splits . trim Nothing) $ transpose $ map pad $ reverse [0 .. n-1]
  where len = length (show (n-1))
        pad i = reverse $ take len $ reverse (show i) ++ repeat ' '

        trim _      "" = ""
        trim mbPrev (c:cs)
          | mbPrev == Just c = ' ' : trim mbPrev   cs
          | True             =  c  : trim (Just c) cs

space :: [Int] -> String -> String
space []     xs = xs
space _      "" = ""
space (i:is) xs = case splitAt i xs of
                   (pre, "")   -> pre
                   (pre, post) -> pre ++ " " ++ space is post
