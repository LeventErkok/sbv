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

{-# LANGUAGE NamedFieldPuns #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}

module Data.SBV.Utils.CrackNum (
        crackNum
      ) where

import Data.SBV.Core.Concrete
import Data.SBV.Core.Kind
import Data.SBV.Core.SizedFloats
import Data.SBV.Utils.Numeric
import Data.SBV.Utils.PrettyNum (showFloatAtBase)

import Data.Char (intToDigit, toUpper, isSpace)

import Data.Bits
import Data.List

import LibBF hiding (Zero, bfToString)

import Numeric

-- | A class for cracking things deeper, if we know how.
class CrackNum a where
  -- | Convert an item to possibly bit-level description, if possible.
  crackNum :: a -> Bool -> Maybe Integer -> Maybe String

-- | CVs are easy to crack
instance CrackNum CV where
  crackNum cv verbose mbIV = case kindOf cv of
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
                               KRational  {}  -> Nothing

                               -- Actual crackables
                               KFloat{}       -> Just $ let CFloat   f = cvVal cv in float verbose mbIV f
                               KDouble{}      -> Just $ let CDouble  d = cvVal cv in float verbose mbIV d
                               KFP{}          -> Just $ let CFP      f = cvVal cv in float verbose mbIV f
                               KBounded sg sz -> Just $ let CInteger i = cvVal cv in int   sg sz i

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

-- Convert bits to the corresponding integer.
getVal :: [Bool] -> Integer
getVal = foldl (\s b -> 2 * s + if b then 1 else 0) 0

-- Show in hex, but pay attention to how wide a field it should be in
mkHex :: [Bool] -> String
mkHex bin = map toUpper $ showHex (getVal bin) ""

-- | Show a sized word/int in detail
int :: Bool -> Int -> Integer -> String
int signed sz v = intercalate "\n" $ ruler ++ info
  where splits = split4 sz

        ruler = map (tab ++) $ mkRuler sz splits

        bitRep :: [[Bool]]
        bitRep = split splits [v `testBit` i | i <- reverse [0 .. sz - 1]]

        flatHex = concatMap mkHex bitRep
        iprec
          | signed = "Signed "   ++ show sz ++ "-bit 2's complement integer"
          | True   = "Unsigned " ++ show sz ++ "-bit word"

        signBit = v `testBit` (sz-1)
        s | signed && signBit = "-"
          | True              = ""

        av = abs v

        info = [ "   Binary layout: " ++ unwords [concatMap (\b -> if b then "1" else "0") is | is <- bitRep]
               , "      Hex layout: " ++ unwords (split (split4 (length flatHex)) flatHex)
               , "            Type: " ++ iprec
               ]
            ++ [ "            Sign: " ++ if signBit then "Negative" else "Positive" | signed]
            ++ [ "          Binary: " ++ s ++ "0b" ++ showIntAtBase 2 intToDigit av ""
               , "           Octal: " ++ s ++ "0o" ++ showOct av ""
               , "         Decimal: " ++ show v
               , "             Hex: " ++ s ++ "0x" ++ showHex av ""
               ]

-- | What kind of Float is this?
data FPKind = Zero       Bool  -- with sign
            | Infty      Bool  -- with sign
            | NaN
            | Subnormal
            | Normal
            deriving Eq

-- | Show instance for Kind, not for reading back!
instance Show FPKind where
  show Zero{}    = "FP_ZERO"
  show Infty{}   = "FP_INFINITE"
  show NaN       = "FP_NAN"
  show Subnormal = "FP_SUBNORMAL"
  show Normal    = "FP_NORMAL"

-- | Find out what kind this float is. We specifically ask
-- the caller to provide if the number is zero, neg-inf, and pos-inf. Why?
-- Because the FP type doesn't have those recognizers that also work with Float/Double.
getKind :: RealFloat a => a -> FPKind
getKind fp
 | fp == 0           = Zero  (isNegativeZero fp)
 | isInfinite fp     = Infty (fp < 0)
 | isNaN fp          = NaN
 | isDenormalized fp = Subnormal
 | True              = Normal

-- Show the value in different bases
showAtBases :: FPKind -> (String, String, String, String) -> Either String (String, String, String, String)
showAtBases k bvs = case k of
                     Zero False  -> Right ("0b0.0",  "0o0.0",  "0.0",  "0x0")
                     Zero True   -> Right ("-0b0.0", "-0o0.0", "-0.0", "-0o0")
                     Infty False -> Left  "Infinity"
                     Infty True  -> Left  "-Infinity"
                     NaN         -> Left  "NaN"
                     Subnormal   -> Right (dropSuffixes bvs)
                     Normal      -> Right (dropSuffixes bvs)
  where dropSuffixes (a, b, c, d) = (bfRemoveRedundantExp a, bfRemoveRedundantExp b, bfRemoveRedundantExp c, bfRemoveRedundantExp d)

-- | Float data for display purposes
data FloatData = FloatData { prec   :: String
                           , eb     :: Int
                           , sb     :: Int
                           , bits   :: Integer
                           , fpKind :: FPKind
                           , fpVals :: Either String (String, String, String, String)
                           }

-- | A simple means to organize different bits and pieces of float data
-- for display purposes
class HasFloatData a where
  getFloatData :: a -> FloatData

-- | Float instance
instance HasFloatData Float where
  getFloatData f = FloatData {
      prec   = "Single"
    , eb     =  8
    , sb     = 24
    , bits   = fromIntegral (floatToWord f)
    , fpKind = k
    , fpVals = showAtBases k (showFloatAtBase 2 f "", showFloatAtBase 8 f "", show f, showFloatAtBase 16 f "")
    }
    where k = getKind f

-- | Double instance
instance HasFloatData Double where
  getFloatData d  = FloatData {
      prec   = "Double"
    , eb     = 11
    , sb     = 53
    , bits   = fromIntegral (doubleToWord d)
    , fpKind = k
    , fpVals = showAtBases k (showFloatAtBase 2 d "", showFloatAtBase 8 d "", show d, showFloatAtBase 16 d "")
    }
    where k = getKind d

-- | Find the exponent values, (exponent value, exponent as stored, bias)
getExponentData :: FloatData -> (Integer, Integer, Integer)
getExponentData FloatData{eb, sb, bits, fpKind} = (expValue, expStored, bias)
  where -- | Bias is 2^(eb-1) - 1
        bias :: Integer
        bias = (2 :: Integer) ^ ((fromIntegral eb :: Integer) - 1) - 1

        -- | Exponent as stored is simply bit extraction
        expStored = getVal [bits `testBit` i | i <- reverse [sb-1 .. sb+eb-2]]

        -- | Exponent value is stored exponent - bias, unless the number is subnormal. In that case it is 1 - bias
        expValue = case fpKind of
                     Subnormal -> 1 - bias
                     _         -> expStored - bias

-- | FP instance
instance HasFloatData FP where
  getFloatData v@(FP eb sb f) = FloatData {
      prec   = case (eb, sb) of
                 ( 5,  11) -> "Half (5 exponent bits, 10 significand bits.)"
                 ( 8,  24) -> "Single (8 exponent bits, 23 significand bits.)"
                 (11,  53) -> "Double (11 exponent bits, 52 significand bits.)"
                 (15, 113) -> "Quad (15 exponent bits, 112 significand bits.)"
                 ( _,   _) -> show eb ++ " exponent bits, " ++ show (sb-1) ++ " significand bit" ++ if sb > 2 then "s" else ""
    , eb     = eb
    , sb     = sb
    , bits   = bfToBits (mkBFOpts eb sb NearEven) f
    , fpKind = k
    , fpVals = showAtBases k (bfToString 2 True True v, bfToString 8 True True v, bfToString 10 True False v, bfToString 16 True True v)
    }
    where opts = mkBFOpts eb sb NearEven
          k | bfIsZero f           = Zero  (bfIsNeg f)
            | bfIsInf f            = Infty (bfIsNeg f)
            | bfIsNaN f            = NaN
            | bfIsSubnormal opts f = Subnormal
            | True                 = Normal

-- | Show a float in detail. mbSurface is the integer equivalent if this is a NaN; so we
-- can represent it faithfully to the original given. Used by crackNum executable.
float :: HasFloatData a => Bool -> Maybe Integer -> a -> String
float verbose mbSurface f = intercalate "\n" $ ruler ++ legend : info
   where fd@FloatData{prec, eb, sb, bits = bitsAsStored, fpKind, fpVals} = getFloatData f

         nanKind = case fpKind of
                     Zero{}    -> False
                     Infty{}   -> False
                     NaN       -> True
                     Subnormal -> False
                     Normal    -> False

         (nanClassifier, bits, nanChanged)
           | nanKind, Just i <- mbSurface = (extraClassifier i,  i,            i /= bitsAsStored)
           | True                         = ("",                 bitsAsStored, False)

         -- Is this surface representation a signaling NaN or a quiet nan?
         -- The test is that the tip bit of the significand is high: If so, quiet. If top bit is low, then signaling.
         extraClassifier :: Integer -> String
         extraClassifier i
           | sb < 2               = ""      -- I don't think this can happen, but just in case
           | i `testBit` (sb - 2) = " (Quiet)"
           | True                 = " (Signaling)"

         splits = [1, eb, sb]
         ruler  = map (tab ++) $ mkRuler (eb + sb) splits

         legend = tab ++ "S " ++ mkTag ('E' : show eb) eb ++ " " ++ mkTag ('S' : show (sb-1)) (sb-1)

         mkTag t len = take len $ replicate ((len - length t) `div` 2) '-' ++ t ++ repeat '-'

         allBits :: [Bool]
         allBits = [bits `testBit` i | i <- reverse [0 .. eb + sb - 1]]

         storedBits :: [Bool]
         storedBits = [bitsAsStored `testBit` i | i <- reverse [0 .. eb + sb - 1]]

         flatHex = concatMap mkHex (split (split4 (eb + sb)) allBits)
         sign    = bits `testBit` (eb+sb-1)

         (exponentVal, storedExponent, bias) = getExponentData fd

         esInfo = "Stored: " ++ show storedExponent ++ ", Bias: " ++ show bias

         chunks bs = unwords [concatMap (\b -> if b then "1" else "0") is | is <- split splits bs]

         isSubNormal = case fpKind of
                         Subnormal -> True
                         _         -> False

         info =   [ "   Binary layout: " ++ chunks allBits]
               ++ [ " Calculated bits: " ++ chunks storedBits ++ " (Surface NaN value differs from calculated)" | verbose && nanChanged]
               ++ [ "      Hex layout: " ++ unwords (split (split4 (length flatHex)) flatHex)
                  , "       Precision: " ++ prec
                  , "            Sign: " ++ if sign then "Negative" else "Positive"
                  ]
               ++ [ "        Exponent: " ++ show exponentVal ++ " (Subnormal, with fixed exponent value. " ++ esInfo ++ ")" | isSubNormal    ]
               ++ [ "        Exponent: " ++ show exponentVal ++ " ("                                       ++ esInfo ++ ")" | not isSubNormal]
               ++ [ "  Classification: " ++ show fpKind ++ nanClassifier]
               ++ (case fpVals of
                     Left val                       -> [ "           Value: " ++ val]
                     Right (bval, oval, dval, hval) -> [ "          Binary: " ++ bval
                                                       , "           Octal: " ++ oval
                                                       , "         Decimal: " ++ dval
                                                       , "             Hex: " ++ hval
                                                       ])
               ++ [ "            Note: Representation for NaN's is not unique" | fpKind == NaN]


-- | Build a ruler with given split points
mkRuler :: Int -> [Int] -> [String]
mkRuler n splits = map (trimRight . unwords . split splits . trim Nothing) $ transpose $ map pad $ reverse [0 .. n-1]
  where len = length (show (n-1))
        pad i = reverse $ take len $ reverse (show i) ++ repeat '0'

        trim _      "" = ""
        trim mbPrev (c:cs)
          | mbPrev == Just c = ' ' : trim mbPrev   cs
          | True             =  c  : trim (Just c) cs

        trimRight = reverse . dropWhile isSpace . reverse

split :: [Int] -> [a] -> [[a]]
split _      [] = []
split []     xs = [xs]
split (i:is) xs = case splitAt i xs of
                   (pre, [])   -> [pre]
                   (pre, post) -> pre : split is post
