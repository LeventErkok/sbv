-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.PrettyNum
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Number representations in hex/bin
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Utils.PrettyNum (
        PrettyNum(..), readBin, shex, chex, shexI, sbin, sbinI
      , showCFloat, showCDouble, showHFloat, showHDouble
      , showSMTFloat, showSMTDouble, smtRoundingMode, cvToSMTLib, mkSkolemZero
      ) where

import Data.Char  (intToDigit, ord)
import Data.Int   (Int8, Int16, Int32, Int64)
import Data.List  (isPrefixOf)
import Data.Maybe (fromJust, fromMaybe, listToMaybe)
import Data.Ratio (numerator, denominator)
import Data.Word  (Word8, Word16, Word32, Word64)
import Numeric    (showIntAtBase, showHex, readInt)

import Data.Numbers.CrackNum (floatToFP, doubleToFP)

import Data.SBV.Core.Data
import Data.SBV.Core.Kind (smtType)
import Data.SBV.Core.AlgReals (algRealToSMTLib2)

import Data.SBV.Utils.Lib (stringToQFS)

-- | PrettyNum class captures printing of numbers in hex and binary formats; also supporting negative numbers.
class PrettyNum a where
  -- | Show a number in hexadecimal (starting with @0x@ and type.)
  hexS :: a -> String
  -- | Show a number in binary (starting with @0b@ and type.)
  binS :: a -> String
  -- | Show a number in hex, without prefix, or types.
  hex :: a -> String
  -- | Show a number in bin, without prefix, or types.
  bin :: a -> String

-- Why not default methods? Because defaults need "Integral a" but Bool is not..
instance PrettyNum Bool where
  {hexS = show; binS = show; hex = show; bin = show}
instance PrettyNum String where
  {hexS = show; binS = show; hex = show; bin = show}
instance PrettyNum Word8 where
  {hexS = shex True True (False,8) ; binS = sbin True True (False,8) ; hex = shex False False (False,8) ; bin = sbin False False (False,8) ;}
instance PrettyNum Int8 where
  {hexS = shex True True (True,8)  ; binS = sbin True True (True,8)  ; hex = shex False False (True,8)  ; bin = sbin False False (True,8)  ;}
instance PrettyNum Word16 where
  {hexS = shex True True (False,16); binS = sbin True True (False,16); hex = shex False False (False,16); bin = sbin False False (False,16);}
instance PrettyNum Int16  where
  {hexS = shex True True (True,16);  binS = sbin True True (True,16) ; hex = shex False False (True,16);  bin = sbin False False (True,16) ;}
instance PrettyNum Word32 where
  {hexS = shex True True (False,32); binS = sbin True True (False,32); hex = shex False False (False,32); bin = sbin False False (False,32);}
instance PrettyNum Int32  where
  {hexS = shex True True (True,32);  binS = sbin True True (True,32) ; hex = shex False False (True,32);  bin = sbin False False (True,32) ;}
instance PrettyNum Word64 where
  {hexS = shex True True (False,64); binS = sbin True True (False,64); hex = shex False False (False,64); bin = sbin False False (False,64);}
instance PrettyNum Int64  where
  {hexS = shex True True (True,64);  binS = sbin True True (True,64) ; hex = shex False False (True,64);  bin = sbin False False (True,64) ;}
instance PrettyNum Integer where
  {hexS = shexI True True; binS = sbinI True True; hex = shexI False False; bin = sbinI False False;}

instance PrettyNum CV where
  hexS cv | isUninterpreted cv = show cv ++ " :: " ++ show (kindOf cv)
          | isBoolean       cv = hexS (cvToBool cv) ++ " :: Bool"
          | isFloat         cv = let CFloat   f = cvVal cv in show f ++ " :: Float\n"  ++ show (floatToFP f)
          | isDouble        cv = let CDouble  d = cvVal cv in show d ++ " :: Double\n" ++ show (doubleToFP d)
          | isReal          cv = let CAlgReal r = cvVal cv in show r ++ " :: Real"
          | isString        cv = let CString  s = cvVal cv in show s ++ " :: String"
          | not (isBounded cv) = let CInteger i = cvVal cv in shexI True True i
          | True               = let CInteger i = cvVal cv in shex  True True (hasSign cv, intSizeOf cv) i

  binS cv | isUninterpreted cv = show cv  ++ " :: " ++ show (kindOf cv)
          | isBoolean       cv = binS (cvToBool cv)  ++ " :: Bool"
          | isFloat         cv = let CFloat   f = cvVal cv in show f ++ " :: Float\n"  ++ show (floatToFP f)
          | isDouble        cv = let CDouble  d = cvVal cv in show d ++ " :: Double\n" ++ show (doubleToFP d)
          | isReal          cv = let CAlgReal r = cvVal cv in show r ++ " :: Real"
          | isString        cv = let CString  s = cvVal cv in show s ++ " :: String"
          | not (isBounded cv) = let CInteger i = cvVal cv in sbinI True True i
          | True               = let CInteger i = cvVal cv in sbin  True True (hasSign cv, intSizeOf cv) i

  hex cv | isUninterpreted cv = show cv
         | isBoolean       cv = hexS (cvToBool cv) ++ " :: Bool"
         | isFloat         cv = let CFloat   f = cvVal cv in show f
         | isDouble        cv = let CDouble  d = cvVal cv in show d
         | isReal          cv = let CAlgReal r = cvVal cv in show r
         | isString        cv = let CString  s = cvVal cv in show s
         | not (isBounded cv) = let CInteger i = cvVal cv in shexI False False i
         | True               = let CInteger i = cvVal cv in shex  False False (hasSign cv, intSizeOf cv) i

  bin cv | isUninterpreted cv = show cv
         | isBoolean       cv = binS (cvToBool cv) ++ " :: Bool"
         | isFloat         cv = let CFloat   f = cvVal cv in show f
         | isDouble        cv = let CDouble  d = cvVal cv in show d
         | isReal          cv = let CAlgReal r = cvVal cv in show r
         | isString        cv = let CString  s = cvVal cv in show s
         | not (isBounded cv) = let CInteger i = cvVal cv in sbinI False False i
         | True               = let CInteger i = cvVal cv in sbin  False False (hasSign cv, intSizeOf cv) i

instance (SymVal a, PrettyNum a) => PrettyNum (SBV a) where
  hexS s = maybe (show s) (hexS :: a -> String) $ unliteral s
  binS s = maybe (show s) (binS :: a -> String) $ unliteral s
  hex  s = maybe (show s) (hex  :: a -> String) $ unliteral s
  bin  s = maybe (show s) (bin  :: a -> String) $ unliteral s

-- | Show as a hexadecimal value. First bool controls whether type info is printed
-- while the second boolean controls wether 0x prefix is printed. The tuple is
-- the signedness and the bit-length of the input. The length of the string
-- will /not/ depend on the value, but rather the bit-length.
shex :: (Show a, Integral a) => Bool -> Bool -> (Bool, Int) -> a -> String
shex shType shPre (signed, size) a
 | a < 0
 = "-" ++ pre ++ pad l (s16 (abs (fromIntegral a :: Integer)))  ++ t
 | True
 = pre ++ pad l (s16 a) ++ t
 where t | shType = " :: " ++ (if signed then "Int" else "Word") ++ show size
         | True   = ""
       pre | shPre = "0x"
           | True  = ""
       l = (size + 3) `div` 4

-- | Show as hexadecimal, but for C programs. We have to be careful about
-- printing min-bounds, since C does some funky casting, possibly losing
-- the sign bit. In those cases, we use the defined constants in <stdint.h>.
-- We also properly append the necessary suffixes as needed.
chex :: (Show a, Integral a) => Bool -> Bool -> (Bool, Int) -> a -> String
chex shType shPre (signed, size) a
   | Just s <- (signed, size, fromIntegral a) `lookup` specials
   = s
   | True
   = shex shType shPre (signed, size) a ++ suffix
  where specials :: [((Bool, Int, Integer), String)]
        specials = [ ((True,  8, fromIntegral (minBound :: Int8)),  "INT8_MIN" )
                   , ((True, 16, fromIntegral (minBound :: Int16)), "INT16_MIN")
                   , ((True, 32, fromIntegral (minBound :: Int32)), "INT32_MIN")
                   , ((True, 64, fromIntegral (minBound :: Int64)), "INT64_MIN")
                   ]
        suffix = case (signed, size) of
                   (False, 16) -> "U"

                   (False, 32) -> "UL"
                   (True,  32) -> "L"

                   (False, 64) -> "ULL"
                   (True,  64) -> "LL"

                   _           -> ""

-- | Show as a hexadecimal value, integer version. Almost the same as shex above
-- except we don't have a bit-length so the length of the string will depend
-- on the actual value.
shexI :: Bool -> Bool -> Integer -> String
shexI shType shPre a
 | a < 0
 = "-" ++ pre ++ s16 (abs a)  ++ t
 | True
 = pre ++ s16 a ++ t
 where t | shType = " :: Integer"
         | True   = ""
       pre | shPre = "0x"
           | True  = ""

-- | Similar to 'shex'; except in binary.
sbin :: (Show a, Integral a) => Bool -> Bool -> (Bool, Int) -> a -> String
sbin shType shPre (signed,size) a
 | a < 0
 = "-" ++ pre ++ pad size (s2 (abs (fromIntegral a :: Integer)))  ++ t
 | True
 = pre ++ pad size (s2 a) ++ t
 where t | shType = " :: " ++ (if signed then "Int" else "Word") ++ show size
         | True   = ""
       pre | shPre = "0b"
           | True  = ""

-- | Similar to 'shexI'; except in binary.
sbinI :: Bool -> Bool -> Integer -> String
sbinI shType shPre a
 | a < 0
 = "-" ++ pre ++ s2 (abs a) ++ t
 | True
 =  pre ++ s2 a ++ t
 where t | shType = " :: Integer"
         | True   = ""
       pre | shPre = "0b"
           | True  = ""

-- | Pad a string to a given length. If the string is longer, then we don't drop anything.
pad :: Int -> String -> String
pad l s = replicate (l - length s) '0' ++ s

-- | Binary printer
s2 :: (Show a, Integral a) => a -> String
s2  v = showIntAtBase 2 dig v "" where dig = fromJust . flip lookup [(0, '0'), (1, '1')]

-- | Hex printer
s16 :: (Show a, Integral a) => a -> String
s16 v = showHex v ""

-- | A more convenient interface for reading binary numbers, also supports negative numbers
readBin :: Num a => String -> a
readBin ('-':s) = -(readBin s)
readBin s = case readInt 2 isDigit cvt s' of
              [(a, "")] -> a
              _         -> error $ "SBV.readBin: Cannot read a binary number from: " ++ show s
  where cvt c = ord c - ord '0'
        isDigit = (`elem` "01")
        s' | "0b" `isPrefixOf` s = drop 2 s
           | True                = s

-- | A version of show for floats that generates correct C literals for nan/infinite. NB. Requires "math.h" to be included.
showCFloat :: Float -> String
showCFloat f
   | isNaN f             = "((float) NAN)"
   | isInfinite f, f < 0 = "((float) (-INFINITY))"
   | isInfinite f        = "((float) INFINITY)"
   | True                = show f ++ "F"

-- | A version of show for doubles that generates correct C literals for nan/infinite. NB. Requires "math.h" to be included.
showCDouble :: Double -> String
showCDouble f
   | isNaN f             = "((double) NAN)"
   | isInfinite f, f < 0 = "((double) (-INFINITY))"
   | isInfinite f        = "((double) INFINITY)"
   | True                = show f

-- | A version of show for floats that generates correct Haskell literals for nan/infinite
showHFloat :: Float -> String
showHFloat f
   | isNaN f             = "((0/0) :: Float)"
   | isInfinite f, f < 0 = "((-1/0) :: Float)"
   | isInfinite f        = "((1/0) :: Float)"
   | True                = show f

-- | A version of show for doubles that generates correct Haskell literals for nan/infinite
showHDouble :: Double -> String
showHDouble d
   | isNaN d             = "((0/0) :: Double)"
   | isInfinite d, d < 0 = "((-1/0) :: Double)"
   | isInfinite d        = "((1/0) :: Double)"
   | True                = show d

-- | A version of show for floats that generates correct SMTLib literals using the rounding mode
showSMTFloat :: RoundingMode -> Float -> String
showSMTFloat rm f
   | isNaN f             = as "NaN"
   | isInfinite f, f < 0 = as "-oo"
   | isInfinite f        = as "+oo"
   | isNegativeZero f    = as "-zero"
   | f == 0              = as "+zero"
   | True                = "((_ to_fp 8 24) " ++ smtRoundingMode rm ++ " " ++ toSMTLibRational (toRational f) ++ ")"
   where as s = "(_ " ++ s ++ " 8 24)"

-- | A version of show for doubles that generates correct SMTLib literals using the rounding mode
showSMTDouble :: RoundingMode -> Double -> String
showSMTDouble rm d
   | isNaN d             = as "NaN"
   | isInfinite d, d < 0 = as "-oo"
   | isInfinite d        = as "+oo"
   | isNegativeZero d    = as "-zero"
   | d == 0              = as "+zero"
   | True                = "((_ to_fp 11 53) " ++ smtRoundingMode rm ++ " " ++ toSMTLibRational (toRational d) ++ ")"
   where as s = "(_ " ++ s ++ " 11 53)"

-- | Show a rational in SMTLib format
toSMTLibRational :: Rational -> String
toSMTLibRational r
   | n < 0
   = "(- (/ "  ++ show (abs n) ++ ".0 " ++ show d ++ ".0))"
   | True
   = "(/ " ++ show n ++ ".0 " ++ show d ++ ".0)"
  where n = numerator r
        d = denominator r

-- | Convert a rounding mode to the format SMT-Lib2 understands.
smtRoundingMode :: RoundingMode -> String
smtRoundingMode RoundNearestTiesToEven = "roundNearestTiesToEven"
smtRoundingMode RoundNearestTiesToAway = "roundNearestTiesToAway"
smtRoundingMode RoundTowardPositive    = "roundTowardPositive"
smtRoundingMode RoundTowardNegative    = "roundTowardNegative"
smtRoundingMode RoundTowardZero        = "roundTowardZero"

-- | Convert a CV to an SMTLib2 compliant value
cvToSMTLib :: RoundingMode -> CV -> String
cvToSMTLib rm x
  | isBoolean       x, CInteger  w      <- cvVal x = if w == 0 then "false" else "true"
  | isUninterpreted x, CUserSort (_, s) <- cvVal x = roundModeConvert s
  | isReal          x, CAlgReal  r      <- cvVal x = algRealToSMTLib2 r
  | isFloat         x, CFloat    f      <- cvVal x = showSMTFloat  rm f
  | isDouble        x, CDouble   d      <- cvVal x = showSMTDouble rm d
  | not (isBounded x), CInteger  w      <- cvVal x = if w >= 0 then show w else "(- " ++ show (abs w) ++ ")"
  | not (hasSign x)  , CInteger  w      <- cvVal x = smtLibHex (intSizeOf x) w
  -- signed numbers (with 2's complement representation) is problematic
  -- since there's no way to put a bvneg over a positive number to get minBound..
  -- Hence, we punt and use binary notation in that particular case
  | hasSign x        , CInteger  w      <- cvVal x = if w == negate (2 ^ intSizeOf x)
                                                     then mkMinBound (intSizeOf x)
                                                     else negIf (w < 0) $ smtLibHex (intSizeOf x) (abs w)
  | isChar x         , CChar c          <- cvVal x = smtLibHex 8 (fromIntegral (ord c))
  | isString x       , CString s        <- cvVal x = '\"' : stringToQFS s ++ "\""
  | isList x         , CList xs         <- cvVal x = smtLibSeq (kindOf x) xs
  | isTuple x        , CTuple xs        <- cvVal x = smtLibTup (kindOf x) xs

  | True = error $ "SBV.cvtCV: Impossible happened: Kind/Value disagreement on: " ++ show (kindOf x, x)
  where roundModeConvert s = fromMaybe s (listToMaybe [smtRoundingMode m | m <- [minBound .. maxBound] :: [RoundingMode], show m == s])
        -- Carefully code hex numbers, SMTLib is picky about lengths of hex constants. For the time
        -- being, SBV only supports sizes that are multiples of 4, but the below code is more robust
        -- in case of future extensions to support arbitrary sizes.
        smtLibHex :: Int -> Integer -> String
        smtLibHex 1  v = "#b" ++ show v
        smtLibHex sz v
          | sz `mod` 4 == 0 = "#x" ++ pad (sz `div` 4) (showHex v "")
          | True            = "#b" ++ pad sz (showBin v "")
           where showBin = showIntAtBase 2 intToDigit
        negIf :: Bool -> String -> String
        negIf True  a = "(bvneg " ++ a ++ ")"
        negIf False a = a

        smtLibSeq :: Kind -> [CVal] -> String
        smtLibSeq k          [] = "(as seq.empty " ++ smtType k ++ ")"
        smtLibSeq (KList ek) xs = let mkSeq  [e]   = e
                                      mkSeq  es    = "(seq.++ " ++ unwords es ++ ")"
                                      mkUnit inner = "(seq.unit " ++ inner ++ ")"
                                  in mkSeq (mkUnit . cvToSMTLib rm . CV ek <$> xs)
        smtLibSeq k _ = error "SBV.cvToSMTLib: Impossible case (smtLibSeq), received kind: " ++ show k

        smtLibTup :: Kind -> [CVal] -> String
        smtLibTup (KTuple []) _  = "SBVTuple0"
        smtLibTup (KTuple ks) xs = "(mkSBVTuple" ++ show (length ks) ++ " " ++ unwords (zipWith (\ek e -> cvToSMTLib rm (CV ek e)) ks xs) ++ ")"
        smtLibTup k           _  = error $ "SBV.cvToSMTLib: Impossible case (smtLibTup), received kind: " ++ show k

        -- anomaly at the 2's complement min value! Have to use binary notation here
        -- as there is no positive value we can provide to make the bvneg work.. (see above)
        mkMinBound :: Int -> String
        mkMinBound i = "#b1" ++ replicate (i-1) '0'

-- | Create a skolem 0 for the kind
mkSkolemZero :: RoundingMode -> Kind -> String
mkSkolemZero _ (KUninterpreted _ (Right (f:_))) = f
mkSkolemZero _ (KUninterpreted s _)             = error $ "SBV.mkSkolemZero: Unexpected uninterpreted sort: " ++ s
mkSkolemZero rm k                               = cvToSMTLib rm (mkConstCV k (0::Integer))
