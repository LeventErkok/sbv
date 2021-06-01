-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Kind
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Core.Kind (
          Kind(..), HasKind(..), constructUKind, smtType, hasUninterpretedSorts
        , BVIsNonZero, ValidFloat, intOfProxy
        , showBaseKind, needsFlattening, RoundingMode(..), smtRoundingMode
        ) where

import qualified Data.Generics as G (Data(..), DataType, dataTypeName, dataTypeOf, tyconUQname, dataTypeConstrs, constrFields)

import Data.Char (isSpace)

import Data.Int
import Data.Word
import Data.SBV.Core.AlgReals

import Data.Proxy
import Data.Kind

import Data.List (isPrefixOf, intercalate)

import Data.Typeable (Typeable)
import Data.Type.Bool
import Data.Type.Equality

import GHC.TypeLits

import Data.SBV.Utils.Lib (isKString)

-- | Kind of symbolic value
data Kind = KBool
          | KBounded !Bool !Int
          | KUnbounded
          | KReal
          | KUserSort String (Maybe [String])  -- name. Uninterpreted, or enumeration constants.
          | KFloat
          | KDouble
          | KFP !Int !Int
          | KChar
          | KString
          | KList Kind
          | KSet  Kind
          | KTuple [Kind]
          | KMaybe  Kind
          | KRational
          | KEither Kind Kind
          deriving (Eq, Ord, G.Data)

-- | The interesting about the show instance is that it can tell apart two kinds nicely; since it conveniently
-- ignores the enumeration constructors. Also, when we construct a 'KUserSort', we make sure we don't use any of
-- the reserved names; see 'constructUKind' for details.
instance Show Kind where
  show KBool              = "SBool"
  show (KBounded False n) = pickType n "SWord" "SWord " ++ show n
  show (KBounded True n)  = pickType n "SInt"  "SInt "  ++ show n
  show KUnbounded         = "SInteger"
  show KReal              = "SReal"
  show (KUserSort s _)    = s
  show KFloat             = "SFloat"
  show KDouble            = "SDouble"
  show (KFP eb sb)        = "SFloatingPoint " ++ show eb ++ " " ++ show sb
  show KString            = "SString"
  show KChar              = "SChar"
  show (KList e)          = "[" ++ show e ++ "]"
  show (KSet  e)          = "{" ++ show e ++ "}"
  show (KTuple m)         = "(" ++ intercalate ", " (show <$> m) ++ ")"
  show (KMaybe k)         = "SMaybe "  ++ kindParen (showBaseKind k)
  show (KEither k1 k2)    = "SEither " ++ kindParen (showBaseKind k1) ++ " " ++ kindParen (showBaseKind k2)
  show KRational          = "SRational"

-- | A version of show for kinds that says Bool instead of SBool
showBaseKind :: Kind -> String
showBaseKind = sh
  where sh k@KBool            = noS (show k)
        sh (KBounded False n) = pickType n "Word" "WordN " ++ show n
        sh (KBounded True n)  = pickType n "Int"  "IntN "  ++ show n
        sh k@KUnbounded       = noS (show k)
        sh k@KReal            = noS (show k)
        sh k@KUserSort{}      = show k     -- Leave user-sorts untouched!
        sh k@KFloat           = noS (show k)
        sh k@KDouble          = noS (show k)
        sh k@KFP{}            = noS (show k)
        sh k@KChar            = noS (show k)
        sh k@KString          = noS (show k)
        sh KRational          = "Rational"
        sh (KList k)          = "[" ++ sh k ++ "]"
        sh (KSet k)           = "{" ++ sh k ++ "}"
        sh (KTuple ks)        = "(" ++ intercalate ", " (map sh ks) ++ ")"
        sh (KMaybe k)         = "Maybe "  ++ kindParen (sh k)
        sh (KEither k1 k2)    = "Either " ++ kindParen (sh k1) ++ " " ++ kindParen (sh k2)

        -- Drop the initial S if it's there
        noS ('S':s) = s
        noS s       = s

-- For historical reasons, we show 8-16-32-64 bit values with no space; others with a space. 
pickType :: Int -> String -> String -> String
pickType i standard other
  | i `elem` [8, 16, 32, 64] = standard
  | True                     = other

-- | Put parens if necessary. This test is rather crummy, but seems to work ok
kindParen :: String -> String
kindParen s@('[':_) = s
kindParen s@('(':_) = s
kindParen s | any isSpace s = '(' : s ++ ")"
            | True          = s

-- | How the type maps to SMT land
smtType :: Kind -> String
smtType KBool           = "Bool"
smtType (KBounded _ sz) = "(_ BitVec " ++ show sz ++ ")"
smtType KUnbounded      = "Int"
smtType KReal           = "Real"
smtType KFloat          = "(_ FloatingPoint  8 24)"
smtType KDouble         = "(_ FloatingPoint 11 53)"
smtType (KFP eb sb)     = "(_ FloatingPoint " ++ show eb ++ " " ++ show sb ++ ")"
smtType KString         = "String"
smtType KChar           = "String"
smtType (KList k)       = "(Seq "   ++ smtType k ++ ")"
smtType (KSet  k)       = "(Array " ++ smtType k ++ " Bool)"
smtType (KUserSort s _) = s
smtType (KTuple [])     = "SBVTuple0"
smtType (KTuple kinds)  = "(SBVTuple" ++ show (length kinds) ++ " " ++ unwords (smtType <$> kinds) ++ ")"
smtType KRational       = "SBVRational"
smtType (KMaybe k)      = "(SBVMaybe " ++ smtType k ++ ")"
smtType (KEither k1 k2) = "(SBVEither "  ++ smtType k1 ++ " " ++ smtType k2 ++ ")"

instance Eq  G.DataType where
   a == b = G.tyconUQname (G.dataTypeName a) == G.tyconUQname (G.dataTypeName b)

instance Ord G.DataType where
   a `compare` b = G.tyconUQname (G.dataTypeName a) `compare` G.tyconUQname (G.dataTypeName b)

-- | Does this kind represent a signed quantity?
kindHasSign :: Kind -> Bool
kindHasSign = \case KBool        -> False
                    KBounded b _ -> b
                    KUnbounded   -> True
                    KReal        -> True
                    KFloat       -> True
                    KDouble      -> True
                    KFP{}        -> True
                    KRational    -> True
                    KUserSort{}  -> False
                    KString      -> False
                    KChar        -> False
                    KList{}      -> False
                    KSet{}       -> False
                    KTuple{}     -> False
                    KMaybe{}     -> False
                    KEither{}    -> False

-- | Construct an uninterpreted/enumerated kind from a piece of data; we distinguish simple enumerations as those
-- are mapped to proper SMT-Lib2 data-types; while others go completely uninterpreted
constructUKind :: forall a. (Read a, G.Data a) => a -> Kind
constructUKind a
  | any (`isPrefixOf` sortName) badPrefixes
  = error $ unlines [ "*** Data.SBV: Cannot construct user-sort with name: " ++ show sortName
                    , "***"
                    , "***  Must not start with any of: " ++ intercalate ", " badPrefixes
                    ]
  | True
  = case (constrs, concatMap G.constrFields constrs) of
      ([], _)  -> KUserSort sortName   Nothing
      (cs, []) -> KUserSort sortName $ Just (map show cs)
      _        -> error $ unlines [ "*** Data.SBV: " ++ sortName ++ " is not an enumeration."
                                  , "***"
                                  , "*** To declare an enumeration, constructors should not have any fields."
                                  , "*** To declare an uninterpreted sort, use a datatype with no constructors."
                                  ]

  where -- make sure we don't step on ourselves:
        -- NB. The sort "RoundingMode" is special. It's treated by SBV as a user-defined
        -- sort, even though it's internally handled differently. So, that name doesn't appear
        -- below.
        badPrefixes = [ "SBool",   "SWord", "SInt", "SInteger", "SReal",  "SFloat", "SDouble"
                      , "SString", "SChar", "[",    "SSet",     "STuple", "SMaybe", "SEither"
                      , "SRational"
                      ]

        dataType    = G.dataTypeOf a
        sortName    = G.tyconUQname . G.dataTypeName $ dataType
        constrs     = G.dataTypeConstrs dataType

-- | A class for capturing values that have a sign and a size (finite or infinite)
-- minimal complete definition: kindOf, unless you can take advantage of the default
-- signature: This class can be automatically derived for data-types that have
-- a 'G.Data' instance; this is useful for creating uninterpreted sorts. So, in
-- reality, end users should almost never need to define any methods.
class HasKind a where
  kindOf      :: a -> Kind
  hasSign     :: a -> Bool
  intSizeOf   :: a -> Int
  isBoolean   :: a -> Bool
  isBounded   :: a -> Bool   -- NB. This really means word/int; i.e., Real/Float will test False
  isReal      :: a -> Bool
  isFloat     :: a -> Bool
  isDouble    :: a -> Bool
  isRational  :: a -> Bool
  isFP        :: a -> Bool
  isUnbounded :: a -> Bool
  isUserSort  :: a -> Bool
  isChar      :: a -> Bool
  isString    :: a -> Bool
  isList      :: a -> Bool
  isSet       :: a -> Bool
  isTuple     :: a -> Bool
  isMaybe     :: a -> Bool
  isEither    :: a -> Bool
  showType    :: a -> String
  -- defaults
  hasSign x = kindHasSign (kindOf x)

  intSizeOf x = case kindOf x of
                  KBool         -> error "SBV.HasKind.intSizeOf((S)Bool)"
                  KBounded _ s  -> s
                  KUnbounded    -> error "SBV.HasKind.intSizeOf((S)Integer)"
                  KReal         -> error "SBV.HasKind.intSizeOf((S)Real)"
                  KFloat        -> 32
                  KDouble       -> 64
                  KFP i j       -> i + j
                  KRational     -> error "SBV.HasKind.intSizeOf((S)Rational)"
                  KUserSort s _ -> error $ "SBV.HasKind.intSizeOf: Uninterpreted sort: " ++ s
                  KString       -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KChar         -> error "SBV.HasKind.intSizeOf((S)Char)"
                  KList ek      -> error $ "SBV.HasKind.intSizeOf((S)List)" ++ show ek
                  KSet  ek      -> error $ "SBV.HasKind.intSizeOf((S)Set)"  ++ show ek
                  KTuple tys    -> error $ "SBV.HasKind.intSizeOf((S)Tuple)" ++ show tys
                  KMaybe k      -> error $ "SBV.HasKind.intSizeOf((S)Maybe)" ++ show k
                  KEither k1 k2 -> error $ "SBV.HasKind.intSizeOf((S)Either)" ++ show (k1, k2)

  isBoolean       (kindOf -> KBool{})      = True
  isBoolean       _                        = False

  isBounded       (kindOf -> KBounded{})   = True
  isBounded       _                        = False

  isReal          (kindOf -> KReal{})      = True
  isReal          _                        = False

  isFloat         (kindOf -> KFloat{})     = True
  isFloat         _                        = False

  isDouble        (kindOf -> KDouble{})    = True
  isDouble        _                        = False

  isFP            (kindOf -> KFP{})        = True
  isFP            _                        = False

  isRational      (kindOf -> KRational{})  = True
  isRational      _                        = False

  isUnbounded     (kindOf -> KUnbounded{}) = True
  isUnbounded     _                        = False

  isUserSort      (kindOf -> KUserSort{})  = True
  isUserSort      _                        = False

  isChar          (kindOf -> KChar{})      = True
  isChar          _                        = False

  isString        (kindOf -> KString{})    = True
  isString        _                        = False

  isList          (kindOf -> KList{})      = True
  isList          _                        = False

  isSet           (kindOf -> KSet{})       = True
  isSet           _                        = False

  isTuple         (kindOf -> KTuple{})     = True
  isTuple         _                        = False

  isMaybe         (kindOf -> KMaybe{})     = True
  isMaybe         _                        = False

  isEither        (kindOf -> KEither{})    = True
  isEither        _                        = False

  showType = show . kindOf

  -- default signature for uninterpreted/enumerated kinds
  default kindOf :: (Read a, G.Data a) => a -> Kind
  kindOf = constructUKind

-- | This instance allows us to use the `kindOf (Proxy @a)` idiom instead of
-- the `kindOf (undefined :: a)`, which is safer and looks more idiomatic.
instance HasKind a => HasKind (Proxy a) where
  kindOf _ = kindOf (undefined :: a)

instance HasKind Bool     where kindOf _ = KBool
instance HasKind Int8     where kindOf _ = KBounded True  8
instance HasKind Word8    where kindOf _ = KBounded False 8
instance HasKind Int16    where kindOf _ = KBounded True  16
instance HasKind Word16   where kindOf _ = KBounded False 16
instance HasKind Int32    where kindOf _ = KBounded True  32
instance HasKind Word32   where kindOf _ = KBounded False 32
instance HasKind Int64    where kindOf _ = KBounded True  64
instance HasKind Word64   where kindOf _ = KBounded False 64
instance HasKind Integer  where kindOf _ = KUnbounded
instance HasKind AlgReal  where kindOf _ = KReal
instance HasKind Rational where kindOf _ = KRational
instance HasKind Float    where kindOf _ = KFloat
instance HasKind Double   where kindOf _ = KDouble
instance HasKind Char     where kindOf _ = KChar

-- | Grab the bit-size from the proxy. If the nat is too large to fit in an int,
-- we throw an error. (This would mean too big of a bit-size, that we can't
-- really deal with in any practical realm.) In fact, even the range allowed
-- by this conversion (i.e., the entire range of a 64-bit int) is just impractical,
-- but it's hard to come up with a better bound.
intOfProxy :: KnownNat n => Proxy n -> Int
intOfProxy p
  | iv == fromIntegral r = r
  | True                 = error $ unlines [ "Data.SBV: Too large bit-vector size: " ++ show iv
                                           , ""
                                           , "No reasonable proof can be performed with such large bit vectors involved,"
                                           , "So, cowardly refusing to proceed any further! Please file this as a"
                                           , "feature request."
                                           ]
  where iv :: Integer
        iv = natVal p

        r :: Int
        r  = fromEnum iv

-- | Do we have a completely uninterpreted sort lying around anywhere?
hasUninterpretedSorts :: Kind -> Bool
hasUninterpretedSorts KBool                  = False
hasUninterpretedSorts KBounded{}             = False
hasUninterpretedSorts KUnbounded             = False
hasUninterpretedSorts KReal                  = False
hasUninterpretedSorts (KUserSort _ (Just _)) = False  -- These are the enumerated sorts, and they are perfectly fine
hasUninterpretedSorts (KUserSort _ Nothing)  = True   -- These are the completely uninterpreted sorts, which we are looking for here
hasUninterpretedSorts KFloat                 = False
hasUninterpretedSorts KDouble                = False
hasUninterpretedSorts KFP{}                  = False
hasUninterpretedSorts KRational              = False
hasUninterpretedSorts KChar                  = False
hasUninterpretedSorts KString                = False
hasUninterpretedSorts (KList k)              = hasUninterpretedSorts k
hasUninterpretedSorts (KSet k)               = hasUninterpretedSorts k
hasUninterpretedSorts (KTuple ks)            = any hasUninterpretedSorts ks
hasUninterpretedSorts (KMaybe k)             = hasUninterpretedSorts k
hasUninterpretedSorts (KEither k1 k2)        = any hasUninterpretedSorts [k1, k2]

instance (Typeable a, HasKind a) => HasKind [a] where
   kindOf x | isKString @[a] x = KString
            | True             = KList (kindOf (Proxy @a))

instance HasKind Kind where
  kindOf = id

instance HasKind () where
  kindOf _ = KTuple []

instance (HasKind a, HasKind b) => HasKind (a, b) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b)]

instance (HasKind a, HasKind b, HasKind c) => HasKind (a, b, c) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c)]

instance (HasKind a, HasKind b, HasKind c, HasKind d) => HasKind (a, b, c, d) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e) => HasKind (a, b, c, d, e) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f) => HasKind (a, b, c, d, e, f) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g) => HasKind (a, b, c, d, e, f, g) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @g)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h) => HasKind (a, b, c, d, e, f, g, h) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @g), kindOf (Proxy @h)]

instance (HasKind a, HasKind b) => HasKind (Either a b) where
  kindOf _ = KEither (kindOf (Proxy @a)) (kindOf (Proxy @b))

instance HasKind a => HasKind (Maybe a) where
  kindOf _ = KMaybe (kindOf (Proxy @a))

-- | Should we ask the solver to flatten the output? This comes in handy so output is parseable
-- Essentially, we're being conservative here and simply requesting flattening anything that has
-- some structure to it.
needsFlattening :: Kind -> Bool
needsFlattening KBool       = False
needsFlattening KBounded{}  = False
needsFlattening KUnbounded  = False
needsFlattening KReal       = False
needsFlattening KUserSort{} = False
needsFlattening KFloat      = False
needsFlattening KDouble     = False
needsFlattening KFP{}       = False
needsFlattening KRational   = False
needsFlattening KChar       = False
needsFlattening KString     = False
needsFlattening KList{}     = True
needsFlattening KSet{}      = True
needsFlattening KTuple{}    = True
needsFlattening KMaybe{}    = True
needsFlattening KEither{}   = True

-- | Catch 0-width cases
type BVZeroWidth = 'Text "Zero-width bit-vectors are not allowed."

-- | Type family to create the appropriate non-zero constraint
type family BVIsNonZero (arg :: Nat) :: Constraint where
   BVIsNonZero 0 = TypeError BVZeroWidth
   BVIsNonZero _ = ()

#include "MachDeps.h"

-- Allowed sizes for floats, imposed by LibBF.
--
-- NB. In LibBF bindings (and libbf itself as well), minimum number of exponent bits is specified as 3. But this
-- seems unnecessarily restrictive; that constant doesn't seem to be used anywhere, and furthermore my tests with sb = 2
-- didn't reveal anything going wrong. I emailed the author of libbf regarding this, and he said:
--
--   I had no clear reason to use BF_EXP_BITS_MIN = 3. So if "2" is OK then
--   why not. The important is that the basic operations are OK. It is likely
--   there are tricky cases in the transcendental operations but even with
--   large exponents libbf may have problems with them !
--
-- So, in SBV, we allow sb == 2. If this proves problematic, change the number below in definition of FP_MIN_EB to 3!
--
-- NB. It would be nice if we could use the LibBF constants expBitsMin, expBitsMax, precBitsMin, precBitsMax
-- for determining the valid range. Unfortunately this doesn't seem to be possible.
-- See <https://stackoverflow.com/questions/51900360/making-a-type-constraint-based-on-runtime-value-of-maxbound-int> for a discussion.
-- So, we use CPP to work-around that.
#define FP_MIN_EB 2
#define FP_MIN_SB 2
#if WORD_SIZE_IN_BITS == 64
#define FP_MAX_EB 61
#define FP_MAX_SB 4611686018427387902
#else
#define FP_MAX_EB 29
#define FP_MAX_SB 1073741822
#endif

-- | Catch an invalid FP.
type InvalidFloat (eb :: Nat) (sb :: Nat)
        =     'Text "Invalid floating point type `SFloatingPoint " ':<>: 'ShowType eb ':<>: 'Text " " ':<>: 'ShowType sb ':<>: 'Text "'"
        ':$$: 'Text ""
        ':$$: 'Text "A valid float of type 'SFloatingPoint eb sb' must satisfy:"
        ':$$: 'Text "     eb `elem` [" ':<>: 'ShowType FP_MIN_EB ':<>: 'Text " .. " ':<>: 'ShowType FP_MAX_EB ':<>: 'Text "]"
        ':$$: 'Text "     sb `elem` [" ':<>: 'ShowType FP_MIN_SB ':<>: 'Text " .. " ':<>: 'ShowType FP_MAX_SB ':<>: 'Text "]"
        ':$$: 'Text ""
        ':$$: 'Text "Given type falls outside of this range, or the sizes are not known naturals."

-- | A valid float has restrictions on eb/sb values.
-- NB. In the below encoding, I found that CPP is very finicky about substitution of the machine-dependent
-- macros. If you try to put the conditionals in the same line, it fails to substitute for some reason. Hence the awkward spacing.
-- Filed this as a bug report for CPPHS at <https://github.com/malcolmwallace/cpphs/issues/25>.
type family ValidFloat (eb :: Nat) (sb :: Nat) :: Constraint where
  ValidFloat (eb :: Nat) (sb :: Nat) = ( KnownNat eb
                                       , KnownNat sb
                                       , If (   (   eb `CmpNat` FP_MIN_EB == 'EQ
                                                 || eb `CmpNat` FP_MIN_EB == 'GT)
                                             && (   eb `CmpNat` FP_MAX_EB == 'EQ
                                                 || eb `CmpNat` FP_MAX_EB == 'LT)
                                             && (   sb `CmpNat` FP_MIN_SB == 'EQ
                                                 || sb `CmpNat` FP_MIN_SB == 'GT)
                                             && (   sb `CmpNat` FP_MAX_SB == 'EQ
                                                 || sb `CmpNat` FP_MAX_SB == 'LT))
                                            (() :: Constraint)
                                            (TypeError (InvalidFloat eb sb))
                                       )

-- | Rounding mode to be used for the IEEE floating-point operations.
-- Note that Haskell's default is 'RoundNearestTiesToEven'. If you use
-- a different rounding mode, then the counter-examples you get may not
-- match what you observe in Haskell.
data RoundingMode = RoundNearestTiesToEven  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the even number.
                                            -- (In this context, /even/ means the lowest-order bit is zero.)
                  | RoundNearestTiesToAway  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the number further away from 0.
                                            -- (That is, for positive values, pick the greater; for negative values, pick the smaller.)
                  | RoundTowardPositive     -- ^ Round towards positive infinity. (Also known as rounding-up or ceiling.)
                  | RoundTowardNegative     -- ^ Round towards negative infinity. (Also known as rounding-down or floor.)
                  | RoundTowardZero         -- ^ Round towards zero. (Also known as truncation.)
                  deriving (Eq, Ord, Show, Read, G.Data, Bounded, Enum)

-- | 'RoundingMode' kind
instance HasKind RoundingMode

-- | Convert a rounding mode to the format SMT-Lib2 understands.
smtRoundingMode :: RoundingMode -> String
smtRoundingMode RoundNearestTiesToEven = "roundNearestTiesToEven"
smtRoundingMode RoundNearestTiesToAway = "roundNearestTiesToAway"
smtRoundingMode RoundTowardPositive    = "roundTowardPositive"
smtRoundingMode RoundTowardNegative    = "roundTowardNegative"
smtRoundingMode RoundTowardZero        = "roundTowardZero"
