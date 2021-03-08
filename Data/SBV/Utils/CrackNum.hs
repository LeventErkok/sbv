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

import Data.Char (intToDigit)

import Data.Bits
import Data.List

import LibBF

import Numeric

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
                  KFloat{}       -> Just $ let CFloat   f     = cvVal cv in float (Just "Single")  8 24 (fromIntegral (floatToWord f))
                  KDouble{}      -> Just $ let CDouble  d     = cvVal cv in float (Just "Double") 11 53 (fromIntegral (doubleToWord d))
                  KFP eb sb      -> Just $ let CFP (FP _ _ f) = cvVal cv in float Nothing         eb sb (bfToBits (mkBFOpts eb sb NearEven) f)
                  KBounded sg sz -> Just $ let CInteger i     = cvVal cv in int   sg sz i

-- How far off the screen we want displayed? Somewhat experimentally found.
tab :: String
tab = replicate 18 ' '

-- Make splits of 4, top one has the remainder
split4 :: Int -> [Int]
split4 n
  | m == 0 =     rest
  | True   = m : rest
  where (d, m) = n `divMod` 4
        rest   = replicate d 4

-- Show in hex, but pay attention to how wide a field it should be in
mkHex :: [Int] -> String
mkHex bin = showHex (foldl (\b s -> 2  * b + s) 0 bin) ""

-- | Show a sized word/int in detail
int :: Bool -> Int -> Integer -> String
int signed sz v = intercalate "\n" $ ruler ++ info
  where splits = split4 sz

        ruler = map (tab ++) $ mkRuler sz splits

        bitRep :: [[Int]]
        bitRep = split splits [if v `testBit` i then 1 else (0::Int) | i <- reverse [0 .. sz - 1]]

        flatHex = concatMap mkHex bitRep
        iprec
          | signed = "Signed "   ++ show sz ++ "-bit 2's complement integer"
          | True   = "Unsigned " ++ show sz ++ "-bit word"

        signBit = v `testBit` (sz-1)
        s | signBit = "-"
          | True    = ""

        av = abs v

        info = [ "   Binary layout: " ++ unwords [concatMap show  is | is <- bitRep]
               , "      Hex layout: " ++ unwords (split (split4 (length flatHex)) flatHex)
               , "            Type: " ++ iprec
               ]
            ++ [ "            Sign: " ++ if signBit then "Negative" else "Positive" | signed]
            ++ [ "    Binary Value: " ++ s ++ "0b" ++ showIntAtBase 2 intToDigit av ""
               , "     Octal Value: " ++ s ++ "0o" ++ showOct av ""
               , "   Decimal Value: " ++ show v
               , "       Hex Value: " ++ s ++ "0x" ++ showHex av ""
               ]

-- | Show a float in detail
float :: Maybe String -> Int -> Int -> Integer -> String
float mbPrec eb sb v = intercalate "\n" $ ruler ++ legend : info
   where splits = [1, eb, sb]
         ruler  = map (tab ++) $ mkRuler (eb + sb) splits

         legend = tab ++ "S " ++ mkTag ('E' : show eb) eb ++ " " ++ mkTag ('S' : show (sb-1)) (sb-1)

         mkTag t len = take len $ replicate ((len - length t) `div` 2) '-' ++ t ++ repeat '-'

         allBits :: [Int]
         allBits = [if v `testBit` i then 1 else (0 :: Int) | i <- reverse [0 .. eb + sb - 1]]

         flatHex = concatMap mkHex (split (split4 (eb + sb)) allBits)
         sign    = v `testBit` (eb+sb-1)

         prec = case (mbPrec, eb, sb) of
                  (Just k,   _,   _) -> k
                  (Nothing,  5,  11) -> "Half   (5 exponent bits, 10 significand bits.)"
                  (Nothing,  8,  24) -> "Single (8 exponent bits, 23 significand bits.)"
                  (Nothing, 11,  53) -> "Double (11 exponent bits, 52 significand bits.)"
                  (Nothing, 15, 113) -> "Quad (15 exponent bits, 112 significand bits.)"
                  (Nothing,  _,   _) -> show eb ++ " exponent bits, " ++ show (sb-1) ++ " significand bit" ++ if sb > 2 then "s" else ""

         info = [ "   Binary layout: " ++ unwords [concatMap show is | is <- split splits allBits]
                , "      Hex layout: " ++ unwords (split (split4 (length flatHex)) flatHex)
                , "       Precision: " ++ prec
                , "            Sign: " ++ if sign then "Negative" else "Positive"
         {-
                , "        Exponent: " ++ show expt ++ " (Stored: " ++ show stExpt ++ ", Bias: " ++ show bias ++ ")"
                , "       Hex-float: " ++ hexVal
                , "           Value: " ++ val
                ]
             ++ [ "            Note: Representation for NaN's is not unique." | isNaNKind kind]
         -}
          ]


-- | Build a ruler with given split points
mkRuler :: Int -> [Int] -> [String]
mkRuler n splits = map (unwords . split splits . trim Nothing) $ transpose $ map pad $ reverse [0 .. n-1]
  where len = length (show (n-1))
        pad i = reverse $ take len $ reverse (show i) ++ repeat ' '

        trim _      "" = ""
        trim mbPrev (c:cs)
          | mbPrev == Just c = ' ' : trim mbPrev   cs
          | True             =  c  : trim (Just c) cs

split :: [Int] -> [a] -> [[a]]
split _      [] = []
split []     xs = [xs]
split (i:is) xs = case splitAt i xs of
                   (pre, [])   -> [pre]
                   (pre, post) -> pre : split is post
