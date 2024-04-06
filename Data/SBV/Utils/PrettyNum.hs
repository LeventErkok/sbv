-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.PrettyNum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Number representations in hex/bin
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}

module Data.SBV.Utils.PrettyNum (
        PrettyNum(..), readBin, shex, chex, shexI, sbin, sbinI
      , showCFloat, showCDouble, showHFloat, showHDouble, showBFloat, showFloatAtBase
      , showSMTFloat, showSMTDouble, smtRoundingMode, cvToSMTLib
      , showNegativeNumber
      ) where

import Data.Bits  ((.&.), countTrailingZeros)
import Data.Char  (intToDigit, ord, chr)
import Data.Int   (Int8, Int16, Int32, Int64)
import Data.List  (isPrefixOf)
import Data.Maybe (fromJust, fromMaybe, listToMaybe)
import Data.Ratio (numerator, denominator)
import Data.Word  (Word8, Word16, Word32, Word64)

import qualified Data.Set as Set

import Numeric (showIntAtBase, showHex, readInt, floatToDigits)
import qualified Numeric as N (showHFloat)

import Data.SBV.Core.Data
import Data.SBV.Core.Kind (smtType, smtRoundingMode, showBaseKind)

import Data.SBV.Core.AlgReals    (algRealToSMTLib2)
import Data.SBV.Core.SizedFloats (fprToSMTLib2, bfToString)

import Data.SBV.Utils.Lib (stringToQFS)

-- | PrettyNum class captures printing of numbers in hex and binary formats; also supporting negative numbers.
class PrettyNum a where
  -- | Show a number in hexadecimal, starting with @0x@ and type.
  hexS :: a -> String
  -- | Show a number in binary, starting with @0b@ and type.
  binS :: a -> String
  -- | Show a number in hexadecimal, starting with @0x@ but no type.
  hexP :: a -> String
  -- | Show a number in binary, starting with @0b@ but no type.
  binP :: a -> String
  -- | Show a number in hex, without prefix, or types.
  hex :: a -> String
  -- | Show a number in bin, without prefix, or types.
  bin :: a -> String

-- Why not default methods? Because defaults need "Integral a" but Bool is not..
instance PrettyNum Bool where
  hexS = show
  binS = show
  hexP = show
  binP = show
  hex  = show
  bin  = show

instance PrettyNum String where
  hexS = show
  binS = show
  hexP = show
  binP = show
  hex  = show
  bin  = show

instance PrettyNum Word8 where
  hexS = shex True  True  (False, 8)
  binS = sbin True  True  (False, 8)

  hexP = shex False True  (False, 8)
  binP = sbin False True  (False, 8)

  hex  = shex False False (False, 8)
  bin  = sbin False False (False, 8)

instance PrettyNum Int8 where
  hexS = shex True  True  (True, 8)
  binS = sbin True  True  (True, 8)

  hexP = shex False True  (True, 8)
  binP = sbin False True  (True, 8)

  hex  = shex False False (True, 8)
  bin  = sbin False False (True, 8)

instance PrettyNum Word16 where
  hexS = shex True  True  (False, 16)
  binS = sbin True  True  (False, 16)

  hexP = shex False True  (False, 16)
  binP = sbin False True  (False, 16)

  hex  = shex False False (False, 16)
  bin  = sbin False False (False, 16)

instance PrettyNum Int16 where
  hexS = shex True  True  (True, 16)
  binS = sbin True  True  (True, 16)

  hexP = shex False True  (True, 16)
  binP = sbin False True  (True, 16)

  hex  = shex False False (True, 16)
  bin  = sbin False False (True, 16)

instance PrettyNum Word32 where
  hexS = shex True  True  (False, 32)
  binS = sbin True  True  (False, 32)

  hexP = shex False True  (False, 32)
  binP = sbin False True  (False, 32)

  hex  = shex False False (False, 32)
  bin  = sbin False False (False, 32)

instance PrettyNum Int32 where
  hexS = shex True  True  (True, 32)
  binS = sbin True  True  (True, 32)

  hexP = shex False True  (True, 32)
  binP = sbin False True  (True, 32)

  hex  = shex False False (True, 32)
  bin  = sbin False False (True, 32)

instance PrettyNum Word64 where
  hexS = shex True  True  (False, 64)
  binS = sbin True  True  (False, 64)

  hexP = shex False True  (False, 64)
  binP = sbin False True  (False, 64)

  hex  = shex False False (False, 64)
  bin  = sbin False False (False, 64)

instance PrettyNum Int64 where
  hexS = shex True  True  (True, 64)
  binS = sbin True  True  (True, 64)

  hexP = shex False True  (True, 64)
  binP = sbin False True  (True, 64)

  hex  = shex False False (True, 64)
  bin  = sbin False False (True, 64)

instance PrettyNum Integer where
  hexS = shexI True  True
  binS = sbinI True  True

  hexP = shexI False True
  binP = sbinI False True

  hex  = shexI False False
  bin  = sbinI False False

shBKind :: HasKind a => a -> String
shBKind a = " :: " ++ showBaseKind (kindOf a)

instance PrettyNum CV where
  hexS cv | isUserSort      cv = shows cv                                               $  shBKind cv
          | isBoolean       cv = hexS (cvToBool cv)                                     ++ shBKind cv
          | isFloat         cv = let CFloat   f = cvVal cv in N.showHFloat f            $  shBKind cv
          | isDouble        cv = let CDouble  d = cvVal cv in N.showHFloat d            $  shBKind cv
          | isFP            cv = let CFP      f = cvVal cv in bfToString 16 True True f ++ shBKind cv
          | isReal          cv = let CAlgReal r = cvVal cv in show r                    ++ shBKind cv
          | isString        cv = let CString  s = cvVal cv in show s                    ++ shBKind cv
          | not (isBounded cv) = let CInteger i = cvVal cv in shexI True True i
          | True               = let CInteger i = cvVal cv in shex  True True (hasSign cv, intSizeOf cv) i

  binS cv | isUserSort      cv = shows cv                                              $  shBKind cv
          | isBoolean       cv = binS (cvToBool cv)                                    ++ shBKind cv
          | isFloat         cv = let CFloat   f = cvVal cv in showBFloat f             $  shBKind cv
          | isDouble        cv = let CDouble  d = cvVal cv in showBFloat d             $  shBKind cv
          | isFP            cv = let CFP      f = cvVal cv in bfToString 2 True True f ++ shBKind cv
          | isReal          cv = let CAlgReal r = cvVal cv in shows r                  $  shBKind cv
          | isString        cv = let CString  s = cvVal cv in shows s                  $  shBKind cv
          | not (isBounded cv) = let CInteger i = cvVal cv in sbinI True True i
          | True               = let CInteger i = cvVal cv in sbin  True True (hasSign cv, intSizeOf cv) i

  hexP cv | isUserSort      cv = show cv
          | isBoolean       cv = hexS (cvToBool cv)
          | isFloat         cv = let CFloat   f = cvVal cv in show f
          | isDouble        cv = let CDouble  d = cvVal cv in show d
          | isFP            cv = let CFP      f = cvVal cv in bfToString 16 True True f
          | isReal          cv = let CAlgReal r = cvVal cv in show r
          | isString        cv = let CString  s = cvVal cv in show s
          | not (isBounded cv) = let CInteger i = cvVal cv in shexI False True i
          | True               = let CInteger i = cvVal cv in shex  False True (hasSign cv, intSizeOf cv) i

  binP cv | isUserSort      cv = show cv
          | isBoolean       cv = binS (cvToBool cv)
          | isFloat         cv = let CFloat   f = cvVal cv in show f
          | isDouble        cv = let CDouble  d = cvVal cv in show d
          | isFP            cv = let CFP      f = cvVal cv in bfToString 2 True True f
          | isReal          cv = let CAlgReal r = cvVal cv in show r
          | isString        cv = let CString  s = cvVal cv in show s
          | not (isBounded cv) = let CInteger i = cvVal cv in sbinI False True i
          | True               = let CInteger i = cvVal cv in sbin  False True (hasSign cv, intSizeOf cv) i

  hex cv  | isUserSort      cv = show cv
          | isBoolean       cv = hexS (cvToBool cv)
          | isFloat         cv = let CFloat   f = cvVal cv in show f
          | isDouble        cv = let CDouble  d = cvVal cv in show d
          | isFP            cv = let CFP      f = cvVal cv in bfToString 16 False True f
          | isReal          cv = let CAlgReal r = cvVal cv in show r
          | isString        cv = let CString  s = cvVal cv in show s
          | not (isBounded cv) = let CInteger i = cvVal cv in shexI False False i
          | True               = let CInteger i = cvVal cv in shex  False False (hasSign cv, intSizeOf cv) i

  bin cv  | isUserSort      cv = show cv
          | isBoolean       cv = binS (cvToBool cv)
          | isFloat         cv = let CFloat   f = cvVal cv in show f
          | isDouble        cv = let CDouble  d = cvVal cv in show d
          | isFP            cv = let CFP      f = cvVal cv in bfToString 2 False True f
          | isReal          cv = let CAlgReal r = cvVal cv in show r
          | isString        cv = let CString  s = cvVal cv in show s
          | not (isBounded cv) = let CInteger i = cvVal cv in sbinI False False i
          | True               = let CInteger i = cvVal cv in sbin  False False (hasSign cv, intSizeOf cv) i

instance (SymVal a, PrettyNum a) => PrettyNum (SBV a) where
  hexS s = maybe (show s) (hexS :: a -> String) $ unliteral s
  binS s = maybe (show s) (binS :: a -> String) $ unliteral s

  hexP s = maybe (show s) (hexP :: a -> String) $ unliteral s
  binP s = maybe (show s) (binP :: a -> String) $ unliteral s

  hex  s = maybe (show s) (hex  :: a -> String) $ unliteral s
  bin  s = maybe (show s) (bin  :: a -> String) $ unliteral s

-- | Show as a hexadecimal value. First bool controls whether type info is printed
-- while the second boolean controls whether 0x prefix is printed. The tuple is
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
   | True                = N.showHFloat f $ "F /* " ++ show f ++ "F */"

-- | A version of show for doubles that generates correct C literals for nan/infinite. NB. Requires "math.h" to be included.
showCDouble :: Double -> String
showCDouble d
   | isNaN d             = "((double) NAN)"
   | isInfinite d, d < 0 = "((double) (-INFINITY))"
   | isInfinite d        = "((double) INFINITY)"
   | True                = N.showHFloat d " /* " ++ show d ++ " */"

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

-- | Show an SBV rational as an SMTLib value. This is used for faithful rationals.
showSMTRational :: Rational -> String
showSMTRational r = "(SBV.Rational " ++ showNegativeNumber (numerator r) ++ " " ++ showNegativeNumber (denominator r) ++ ")"

-- | Show a rational in SMTLib format. This is used for conversions from regular rationals.
toSMTLibRational :: Rational -> String
toSMTLibRational r
   | n < 0
   = "(- (/ "  ++ show (abs n) ++ ".0 " ++ show d ++ ".0))"
   | True
   = "(/ " ++ show n ++ ".0 " ++ show d ++ ".0)"
  where n = numerator r
        d = denominator r

-- | Convert a CV to an SMTLib2 compliant value
cvToSMTLib :: RoundingMode -> CV -> String
cvToSMTLib rm x
  | isBoolean       x, CInteger  w      <- cvVal x = if w == 0 then "false" else "true"
  | isUserSort      x, CUserSort (_, s) <- cvVal x = roundModeConvert s
  | isReal          x, CAlgReal  r      <- cvVal x = algRealToSMTLib2 r
  | isFloat         x, CFloat    f      <- cvVal x = showSMTFloat  rm f
  | isDouble        x, CDouble   d      <- cvVal x = showSMTDouble rm d
  | isRational      x, CRational r      <- cvVal x = showSMTRational r
  | isFP            x, CFP       f      <- cvVal x = fprToSMTLib2 f
  | not (isBounded x), CInteger  w      <- cvVal x = if w >= 0 then show w else "(- " ++ show (abs w) ++ ")"
  | not (hasSign x)  , CInteger  w      <- cvVal x = smtLibHex (intSizeOf x) w
  -- signed numbers (with 2's complement representation) is problematic
  -- since there's no way to put a bvneg over a positive number to get minBound..
  -- Hence, we punt and use binary notation in that particular case
  | hasSign x        , CInteger  w      <- cvVal x = if w == negate (2 ^ intSizeOf x)
                                                     then mkMinBound (intSizeOf x)
                                                     else negIf (w < 0) $ smtLibHex (intSizeOf x) (abs w)
  | isChar x         , CChar c          <- cvVal x = "(_ char " ++ smtLibHex 8 (fromIntegral (ord c)) ++ ")"
  | isString x       , CString s        <- cvVal x = '\"' : stringToQFS s ++ "\""
  | isList x         , CList xs         <- cvVal x = smtLibSeq (kindOf x) xs
  | isSet x          , CSet s           <- cvVal x = smtLibSet (kindOf x) s
  | isTuple x        , CTuple xs        <- cvVal x = smtLibTup (kindOf x) xs
  | isMaybe x        , CMaybe mc        <- cvVal x = smtLibMaybe  (kindOf x) mc
  | isEither x       , CEither ec       <- cvVal x = smtLibEither (kindOf x) ec

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

        smtLibSet :: Kind -> RCSet CVal -> String
        smtLibSet k set = case set of
                            RegularSet    rs -> Set.foldr' (modify "true")  (start "false") rs
                            ComplementSet rs -> Set.foldr' (modify "false") (start "true")  rs
          where ke = case k of
                       KSet ek -> ek
                       _       -> error $ "SBV.cvToSMTLib: Impossible case (smtLibSet), received kind: " ++ show k

                start def = "((as const " ++ smtType k ++ ") " ++ def ++ ")"

                modify how e s = "(store " ++ s ++ " " ++ cvToSMTLib rm (CV ke e) ++ " " ++ how ++ ")"

        smtLibTup :: Kind -> [CVal] -> String
        smtLibTup (KTuple []) _  = "mkSBVTuple0"
        smtLibTup (KTuple ks) xs = "(mkSBVTuple" ++ show (length ks) ++ " " ++ unwords (zipWith (\ek e -> cvToSMTLib rm (CV ek e)) ks xs) ++ ")"
        smtLibTup k           _  = error $ "SBV.cvToSMTLib: Impossible case (smtLibTup), received kind: " ++ show k

        dtConstructor fld []   res =  "(as " ++ fld ++ " " ++ smtType res ++ ")"
        dtConstructor fld args res = "((as " ++ fld ++ " " ++ smtType res ++ ") " ++ unwords args ++ ")"

        smtLibMaybe :: Kind -> Maybe CVal -> String
        smtLibMaybe km@KMaybe{}   Nothing   = dtConstructor "nothing_SBVMaybe" []                       km
        smtLibMaybe km@(KMaybe k) (Just  c) = dtConstructor "just_SBVMaybe"    [cvToSMTLib rm (CV k c)] km
        smtLibMaybe k             _         = error $ "SBV.cvToSMTLib: Impossible case (smtLibMaybe), received kind: " ++ show k

        smtLibEither :: Kind -> Either CVal CVal -> String
        smtLibEither ke@(KEither  k _) (Left c)  = dtConstructor "left_SBVEither"  [cvToSMTLib rm (CV k c)] ke
        smtLibEither ke@(KEither  _ k) (Right c) = dtConstructor "right_SBVEither" [cvToSMTLib rm (CV k c)] ke
        smtLibEither k                 _         = error $ "SBV.cvToSMTLib: Impossible case (smtLibEither), received kind: " ++ show k

        -- anomaly at the 2's complement min value! Have to use binary notation here
        -- as there is no positive value we can provide to make the bvneg work.. (see above)
        mkMinBound :: Int -> String
        mkMinBound i = "#b1" ++ replicate (i-1) '0'

-- | Show a float as a binary
showBFloat :: (Show a, RealFloat a) => a -> ShowS
showBFloat = showFloatAtBase 2

-- | Like Haskell's showHFloat, but uses arbitrary base instead.
-- Note that the exponent is always written in decimal. Let the exponent value be d:
--    If base=10, then we use @e@ to denote the exponent; meaning 10^d
--    If base is a power of 2, then we use @p@ to denote the exponent; meaning 2^d
--    Otherwise, we use @ to denote the exponent, and it means base^d
showFloatAtBase :: (Show a, RealFloat a) => Int -> a -> ShowS
showFloatAtBase base input
  | base < 2 = error $ "showFloatAtBase: Received invalid base (must be >= 2): " ++ show base
  | True     = showString $ fmt input
  where fmt x
         | isNaN x                   = "NaN"
         | isInfinite x              = (if x < 0 then "-" else "") ++ "Infinity"
         | x < 0 || isNegativeZero x = '-' : cvt (-x)
         | True                      = cvt x

        basePow2 = base .&. (base-1) == 0
        lg2Base  = countTrailingZeros base  -- only used when basePow2 is true

        prefix = case base of
                   2  -> "0b"
                   8  -> "0o"
                   10 -> ""
                   16 -> "0x"
                   x  -> "0<" ++ show x ++ ">"

        powChar
          | base == 10 = 'e'
          | basePow2   = 'p'
          | True       = '@'

        -- why r-1? Because we're shifting the fraction by 1 digit; does reducing the exponent by 1
        f2d x = case floatToDigits (fromIntegral base) x of
                  ([],   e) -> (0, [], e - 1)
                  (d:ds, e) -> (d, ds, e - 1)

        cvt x
         | x == 0 = prefix ++ '0' : powChar : "+0"
         | True   = prefix ++ toDigit d ++ frac ds ++ pow
         where (d, ds, e)  = f2d x
               pow
                | base == 10 = powChar : shSigned e
                | basePow2   = powChar : shSigned (e * lg2Base)
                | True       = powChar : shSigned e

               shSigned v
                | v < 0      =       show v
                | True       = '+' : show v

        -- Given digits, show them except if they're all 0 then drop
        frac digits
         | all (== 0) digits = ""
         | True              = "." ++ concatMap toDigit digits

        toDigit v | v <= 15 = [intToDigit v]
                  | v <  36 = [chr (ord 'a' + v - 10)]
                  | True    = '<' : show v ++ ">"

-- | When we show a negative number in SMTLib, we must properly parenthesize.
showNegativeNumber :: (Show a, Num a, Ord a) => a -> String
showNegativeNumber i
  | i < 0 = "(- " ++ show (-i) ++ ")"
  | True  = show i
