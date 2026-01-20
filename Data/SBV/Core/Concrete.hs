-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Concrete
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Operations on concrete values
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.Concrete where

import Control.Monad (replicateM)

import Control.DeepSeq (NFData)

import Data.Bits
import System.Random (randomIO, randomRIO)

import Data.Char (chr, isSpace)
import Data.List (intercalate)
import qualified Data.Text as T

import Data.SBV.Core.Kind
import Data.SBV.Core.AlgReals
import Data.SBV.Core.SizedFloats

import Data.Proxy

import Data.SBV.Utils.Numeric (fpIsEqualObjectH, fpCompareObjectH)

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Generics as G

import GHC.Generics

import Test.QuickCheck (Arbitrary(..))

-- | A 'RCSet' is either a regular set or a set given by its complement from the corresponding universal set.
data RCSet a = RegularSet    (Set a)
             | ComplementSet (Set a)
             deriving (NFData, G.Data, Generic)

instance (Ord a, Arbitrary a) => Arbitrary (RCSet a) where
  arbitrary = do c :: Bool <- arbitrary
                 if c then RegularSet    <$> arbitrary
                      else ComplementSet <$> arbitrary

-- | Show instance. Regular sets are shown as usual.
-- Complements are shown "U -" notation.
instance Show a => Show (RCSet a) where
  show rcs = case rcs of
               ComplementSet s | Set.null s -> "U"
                               | True       -> "U - " ++ sh (Set.toAscList s)
               RegularSet    s              ->           sh (Set.toAscList s)
   where sh xs = '{' : intercalate "," (map show xs) ++ "}"

-- | Structural equality for 'RCSet'. We need Eq/Ord instances for 'RCSet' because we want to put them in maps/tables. But
-- we don't want to derive these, nor make it an instance! Why? Because the same set can have multiple representations if the underlying
-- type is finite. For instance, @{True} = U - {False}@ for boolean sets! Instead, we use the following two functions,
-- which are equivalent to Eq/Ord instances and work for our purposes, but we do not export these to the user.
eqRCSet :: Eq a => RCSet a -> RCSet a -> Bool
eqRCSet (RegularSet    a) (RegularSet    b) = a == b
eqRCSet (ComplementSet a) (ComplementSet b) = a == b
eqRCSet _                 _                 = False

-- | Comparing 'RCSet' values. See comments for 'eqRCSet' on why we don't define the 'Ord' instance.
compareRCSet :: Ord a => RCSet a -> RCSet a -> Ordering
compareRCSet (RegularSet    a) (RegularSet    b) = a `compare` b
compareRCSet (RegularSet    _) (ComplementSet _) = LT
compareRCSet (ComplementSet _) (RegularSet    _) = GT
compareRCSet (ComplementSet a) (ComplementSet b) = a `compare` b

instance HasKind a => HasKind (RCSet a) where
  kindOf _ = KSet (kindOf (Proxy @a))

-- | Underlying type for SMTLib arrays, as a list of key-value pairs, with a default for unmapped
-- elements. Note that this type matches the typical models returned by SMT-solvers.
-- When we store the array, we do not bother removing earlier writes, so there might be duplicates.
-- That is, we store the history of the writes. The earlier a pair is in the list, the "later" it
-- is done, i.e., it takes precedence over the latter entries.
data ArrayModel a b = ArrayModel [(a, b)] b
                     deriving (G.Data, Generic, NFData, Show)

-- | The kind of an ArrayModel
instance (HasKind a, HasKind b) => HasKind (ArrayModel a b) where
   kindOf _ = KArray (kindOf (Proxy @a)) (kindOf (Proxy @b))

-- | A constant value.
-- Note: If you add a new constructor here, make sure you add the
-- corresponding equality in the instance "Eq CVal" and "Ord CVal"!
data CVal = CAlgReal  !AlgReal                 -- ^ Algebraic real
          | CInteger  !Integer                 -- ^ Bit-vector/unbounded integer
          | CFloat    !Float                   -- ^ Float
          | CDouble   !Double                  -- ^ Double
          | CFP       !FP                      -- ^ Arbitrary float
          | CRational Rational                 -- ^ Rational
          | CChar     !Char                    -- ^ Character
          | CString   !String                  -- ^ String
          | CList     ![CVal]                  -- ^ List
          | CSet      !(RCSet CVal)            -- ^ Set. Can be regular or complemented.
          | CADT      (String, [(Kind, CVal)]) -- ^ ADT: Constructor, and fields
          | CTuple    ![CVal]                  -- ^ Tuple
          | CArray    !(ArrayModel CVal CVal)  -- ^ Arrays are backed by look-up tables concretely
          deriving (G.Data, Generic, NFData)

-- | Assign a rank to constant values, this is structural and helps with ordering
cvRank :: CVal -> Int
cvRank CAlgReal  {} =  0
cvRank CInteger  {} =  1
cvRank CFloat    {} =  2
cvRank CDouble   {} =  3
cvRank CFP       {} =  4
cvRank CRational {} =  5
cvRank CChar     {} =  6
cvRank CString   {} =  7
cvRank CList     {} =  8
cvRank CSet      {} =  9
cvRank CADT      {} = 10
cvRank CTuple    {} = 11
cvRank CArray    {} = 12

-- | Eq instance for CVal. Note that we cannot simply derive Eq/Ord, since CVAlgReal doesn't have proper
-- instances for these when values are infinitely precise reals. However, we do
-- need a structural eq/ord for Map indexes; so define custom ones here:
instance Eq CVal where
  CAlgReal  a == CAlgReal  b = a `algRealStructuralEqual` b
  CInteger  a == CInteger  b = a == b
  CFloat    a == CFloat    b = a `fpIsEqualObjectH` b   -- We don't want +0/-0 to be confused; and also we want NaN = NaN here!
  CDouble   a == CDouble   b = a `fpIsEqualObjectH` b   -- ditto
  CRational a == CRational b = a == b
  CFP       a == CFP       b = a `arbFPIsEqualObjectH` b
  CChar     a == CChar     b = a == b
  CString   a == CString   b = a == b
  CList     a == CList     b = a == b
  CSet      a == CSet      b = a `eqRCSet` b
  CTuple    a == CTuple    b = a == b
  CADT      a == CADT      b = a == b

  -- This is legit since we don't use this equality for actual semantic" equality, but rather as an index into maps
  CArray    (ArrayModel a1 d1) == CArray (ArrayModel a2 d2) = (a1, d1) == (a2, d2)

  a           == b           = if cvRank a == cvRank b
                                  then error $ unlines [ ""
                                                       , "*** Data.SBV.Eq.CVal: Impossible happened: same rank in comparison fallthru"
                                                       , "***"
                                                       , "***   Received: " ++ show (cvRank a, cvRank b)
                                                       , "***"
                                                       , "*** Please report this as a bug!"
                                                       ]
                                  else False

-- | Ord instance for CVal. Same comments as the 'Eq' instance why this cannot be derived.
instance Ord CVal where
  CAlgReal  a `compare` CAlgReal  b = a `algRealStructuralCompare` b
  CInteger  a `compare` CInteger  b = a `compare`                  b
  CFloat    a `compare` CFloat    b = a `fpCompareObjectH`         b
  CDouble   a `compare` CDouble   b = a `fpCompareObjectH`         b
  CRational a `compare` CRational b = a `compare`                  b
  CFP       a `compare` CFP       b = a `arbFPCompareObjectH`      b
  CChar     a `compare` CChar     b = a `compare`                  b
  CString   a `compare` CString   b = a `compare`                  b
  CList     a `compare` CList     b = a `compare`                  b
  CSet      a `compare` CSet      b = a `compareRCSet`             b
  CTuple    a `compare` CTuple    b = a `compare`                  b
  CADT      a `compare` CADT      b = a `compare`                  b

  -- This is legit since we don't use this equality for actual semantic order, but rather as an index into maps
  CArray    (ArrayModel a1 d1) `compare` CArray (ArrayModel a2 d2) = (a1, d1) `compare` (a2, d2)

  a           `compare` b           = let ra = cvRank a
                                          rb = cvRank b
                                      in if ra == rb
                                            then error $ unlines [ ""
                                                                 , "*** Data.SBV.Ord.CVal: Impossible happened: same rank in comparison fallthru"
                                                                 , "***"
                                                                 , "***   Received: " ++ show (ra, rb)
                                                                 , "***"
                                                                 , "*** Please report this as a bug!"
                                                                 ]
                                            else cvRank a `compare` cvRank b

-- | A t'CV' represents a concrete word of a fixed size:
-- For signed words, the most significant digit is considered to be the sign.
data CV = CV { cvKind  :: !Kind
             , cvVal   :: !CVal
             }
             deriving (Eq, Ord, G.Data, NFData, Generic)

-- | A generalized CV allows for expressions involving infinite and epsilon values/intervals Used in optimization problems.
data GeneralizedCV = ExtendedCV ExtCV
                   | RegularCV  CV

-- | A simple expression type over extended values, covering infinity, epsilon and intervals.
data ExtCV = Infinite  Kind         -- infinity
           | Epsilon   Kind         -- epsilon
           | Interval  ExtCV ExtCV  -- closed interval
           | BoundedCV CV           -- a bounded value (i.e., neither infinity, nor epsilon). Note that this cannot appear at top, but can appear as a sub-expr.
           | AddExtCV  ExtCV ExtCV  -- addition
           | MulExtCV  ExtCV ExtCV  -- multiplication

-- | Kind instance for Extended CV
instance HasKind ExtCV where
  kindOf (Infinite  k)   = k
  kindOf (Epsilon   k)   = k
  kindOf (Interval  l _) = kindOf l
  kindOf (BoundedCV  c)  = kindOf c
  kindOf (AddExtCV  l _) = kindOf l
  kindOf (MulExtCV  l _) = kindOf l

-- | Show instance, shows with the kind
instance Show ExtCV where
  show = showExtCV True

-- | Show an extended CV, with kind if required
showExtCV :: Bool -> ExtCV -> String
showExtCV = go False
  where go parens shk extCV = case extCV of
                                Infinite{}    -> withKind False "oo"
                                Epsilon{}     -> withKind False "epsilon"
                                Interval  l u -> withKind True  $ '['  : showExtCV False l ++ " .. " ++ showExtCV False u ++ "]"
                                BoundedCV c   -> showCV shk c
                                AddExtCV l r  -> par $ withKind False $ add (go True False l) (go True False r)

                                -- a few niceties here to grok -oo and -epsilon
                                MulExtCV (BoundedCV (CV KUnbounded (CInteger (-1)))) Infinite{} -> withKind False "-oo"
                                MulExtCV (BoundedCV (CV KReal      (CAlgReal (-1)))) Infinite{} -> withKind False "-oo"
                                MulExtCV (BoundedCV (CV KUnbounded (CInteger (-1)))) Epsilon{}  -> withKind False "-epsilon"
                                MulExtCV (BoundedCV (CV KReal      (CAlgReal (-1)))) Epsilon{}  -> withKind False "-epsilon"

                                MulExtCV l r  -> par $ withKind False $ mul (go True False l) (go True False r)
           where par v | parens = '(' : v ++ ")"
                       | True   = v
                 withKind isInterval v | not shk    = v
                                       | isInterval = v ++ " :: [" ++ T.unpack (showBaseKind (kindOf extCV)) ++ "]"
                                       | True       = v ++ " :: "  ++ T.unpack (showBaseKind (kindOf extCV))

                 add :: String -> String -> String
                 add n ('-':v) = n ++ " - " ++ v
                 add n v       = n ++ " + " ++ v

                 mul :: String -> String -> String
                 mul n v = n ++ " * " ++ v

-- | Is this a regular CV?
isRegularCV :: GeneralizedCV -> Bool
isRegularCV RegularCV{}  = True
isRegularCV ExtendedCV{} = False

-- | 'Kind' instance for CV
instance HasKind CV where
  kindOf (CV k _) = k

-- | 'Kind' instance for generalized CV
instance HasKind GeneralizedCV where
  kindOf (ExtendedCV e) = kindOf e
  kindOf (RegularCV  c) = kindOf c

-- | Are two CV's of the same type?
cvSameType :: CV -> CV -> Bool
cvSameType x y = kindOf x == kindOf y

-- | Convert a CV to a Haskell boolean (NB. Assumes input is well-kinded)
cvToBool :: CV -> Bool
cvToBool x = cvVal x /= CInteger 0

-- | Normalize a CV. Essentially performs modular arithmetic to make sure the
-- value can fit in the given bit-size. Note that this is rather tricky for
-- negative values, due to asymmetry. (i.e., an 8-bit negative number represents
-- values in the range -128 to 127; thus we have to be careful on the negative side.)
normCV :: CV -> CV
normCV c@(CV (KBounded signed sz) (CInteger v)) = c { cvVal = CInteger norm }
 where norm | sz == 0 = 0

            | signed  = let rg = 2 ^ (sz - 1)
                        in case divMod v rg of
                                  (a, b) | even a -> b
                                  (_, b)          -> b - rg

            | True    = {- We really want to do:

                                v `mod` (2 ^ sz)

                           Below is equivalent, and hopefully faster!
                        -}
                        v .&. (((1 :: Integer) `shiftL` sz) - 1)
normCV c@(CV KBool (CInteger v)) = c { cvVal = CInteger (v .&. 1) }
normCV c                         = c
{-# INLINE normCV #-}

-- | Constant False as a t'CV'. We represent it using the integer value 0.
falseCV :: CV
falseCV = CV KBool (CInteger 0)

-- | Constant True as a t'CV'. We represent it using the integer value 1.
trueCV :: CV
trueCV  = CV KBool (CInteger 1)

-- | Map a unary function through a t'CV'.
mapCV :: (AlgReal             -> AlgReal)
      -> (Integer             -> Integer)
      -> (Float               -> Float)
      -> (Double              -> Double)
      -> (FP                  -> FP)
      -> (Rational            -> Rational)
      -> CV                   -> CV
mapCV r i f d af ra x  = normCV $ CV (kindOf x) $ case cvVal x of
                                                    CAlgReal  a -> CAlgReal  (r  a)
                                                    CInteger  a -> CInteger  (i  a)
                                                    CFloat    a -> CFloat    (f  a)
                                                    CDouble   a -> CDouble   (d  a)
                                                    CFP       a -> CFP       (af a)
                                                    CRational a -> CRational (ra a)
                                                    CChar{}     -> error "Data.SBV.mapCV: Unexpected call through mapCV with chars!"
                                                    CString{}   -> error "Data.SBV.mapCV: Unexpected call through mapCV with strings!"
                                                    CADT{}      -> error "Data.SBV.mapCV: Unexpected call through mapCV with ADTs!"
                                                    CList{}     -> error "Data.SBV.mapCV: Unexpected call through mapCV with lists!"
                                                    CSet{}      -> error "Data.SBV.mapCV: Unexpected call through mapCV with sets!"
                                                    CTuple{}    -> error "Data.SBV.mapCV: Unexpected call through mapCV with tuples!"
                                                    CArray{}    -> error "Data.SBV.mapCV: Unexpected call through mapCV with arrays!"

-- | Map a binary function through a t'CV'.
mapCV2 :: (AlgReal             -> AlgReal             -> AlgReal)
       -> (Integer             -> Integer             -> Integer)
       -> (Float               -> Float               -> Float)
       -> (Double              -> Double              -> Double)
       -> (FP                  -> FP                  -> FP)
       -> (Rational            -> Rational            -> Rational)
       -> CV                   -> CV                  -> CV
mapCV2 r i f d af ra x y = case (cvSameType x y, cvVal x, cvVal y) of
                            (True, CAlgReal  a, CAlgReal  b) -> normCV $ CV (kindOf x) (CAlgReal  (r  a b))
                            (True, CInteger  a, CInteger  b) -> normCV $ CV (kindOf x) (CInteger  (i  a b))
                            (True, CFloat    a, CFloat    b) -> normCV $ CV (kindOf x) (CFloat    (f  a b))
                            (True, CDouble   a, CDouble   b) -> normCV $ CV (kindOf x) (CDouble   (d  a b))
                            (True, CFP       a, CFP       b) -> normCV $ CV (kindOf x) (CFP       (af a b))
                            (True, CRational a, CRational b) -> normCV $ CV (kindOf x) (CRational (ra a b))
                            (True, CChar{},     CChar{})     -> unexpected "chars!"
                            (True, CString{},   CString{})   -> unexpected "strings!"
                            (True, CList{},     CList{})     -> unexpected "lists!"
                            (True, CTuple{},    CTuple{})    -> unexpected "tuples!"
                            _                                -> unexpected $ "incompatible args: " ++ show (x, y)
   where unexpected w = error $ unlines [ ""
                                        , "*** Data.SBV.mapCV2: Unexpected call through mapCV2 with " ++ w
                                        , "*** Please report this as a bug!"
                                        ]

-- | Show instance for t'CV'.
instance Show CV where
  show = showCV True

-- | Show instance for Generalized t'CV'
instance Show GeneralizedCV where
  show (ExtendedCV k) = showExtCV True k
  show (RegularCV  c) = showCV    True c

-- | Show a CV, with kind info if bool is True
showCV :: Bool -> CV -> String
showCV shk w | isBoolean w = show (cvToBool w) ++ (if shk then " :: Bool" else "")
showCV shk w = sh (cvVal w) ++ kInfo
  where kInfo | shk  = " :: " ++ T.unpack (showBaseKind wk)
              | True = ""

        wk = kindOf w

        sh (CAlgReal  v) = show  v
        sh (CInteger  v) = show  v
        sh (CFloat    v) = show  v
        sh (CDouble   v) = show  v
        sh (CFP       v) = show  v
        sh (CRational v) = show  v
        sh (CChar     v) = show  v
        sh (CString   v) = show  v
        sh (CADT      c) = shADT c
        sh (CList     v) = shL   v
        sh (CSet      v) = shS   v
        sh (CTuple    v) = shT   v
        sh (CArray    v) = shA   v

        shL xs = "[" ++ intercalate "," (map (showCV False . CV ke) xs) ++ "]"
          where ke = case wk of
                       KList k -> k
                       _       -> error $ "Data.SBV.showCV: Impossible happened, expected list, got: " ++ show wk

        -- we represent complements as @U - set@. This might be confusing, but is utterly cute!
        shS :: RCSet CVal -> String
        shS eru = case eru of
                    RegularSet    e              -> set e
                    ComplementSet e | Set.null e -> "U"
                                    | True       -> "U - " ++ set e
          where set xs = "{" ++ intercalate "," (map (showCV False . CV ke) (Set.toList xs)) ++ "}"
                ke = case wk of
                       KSet k -> k
                       _      -> error $ "Data.SBV.showCV: Impossible happened, expected set, got: " ++ show wk

        shT :: [CVal] -> String
        shT xs = "(" ++ intercalate "," xs' ++ ")"
          where xs' = case wk of
                        KTuple ks | length ks == length xs -> zipWith (\k x -> showCV False (CV k x)) ks xs
                        _   -> error $ "Data.SBV.showCV: Impossible happened, expected tuple (of length " ++ show (length xs) ++ "), got: " ++ show wk

        shA :: ArrayModel CVal CVal -> String
        shA (ArrayModel assocs def)
          | KArray k1 k2 <- wk = "([" ++ intercalate "," [showCV False (CV (KTuple [k1, k2]) (CTuple [a, b])) | (a, b) <- assocs] ++ "], " ++ showCV False (CV k2 def) ++ ")"
          | True               = error $ "Data.SBV.showCV: Impossible happened, expected array, got: " ++ show wk

        shADT (c, kvs)
          | null @[] flds = c
          | True          = unwords (c : map wrap flds)
          where wrap v
                 | take 1 v `elem` ["(", "[", "{"]  = v
                 | any isSpace v || take 1 v == "-" = '(' : v ++ ")"
                 | True                             = v

                flds = map (\(k, v) -> showCV False (CV k v)) kvs

-- | Create a constant word from an integral.
mkConstCV :: Integral a => Kind -> a -> CV
mkConstCV k@KVar{}        _ = error $ "mkConstCV: Unexpected kind: " ++ show k
mkConstCV KBool           a = normCV $ CV KBool      (CInteger  (toInteger a))
mkConstCV k@KBounded{}    a = normCV $ CV k          (CInteger  (toInteger a))
mkConstCV KUnbounded      a = normCV $ CV KUnbounded (CInteger  (toInteger a))
mkConstCV KReal           a = normCV $ CV KReal      (CAlgReal  (fromInteger (toInteger a)))
mkConstCV KFloat          a = normCV $ CV KFloat     (CFloat    (fromInteger (toInteger a)))
mkConstCV KDouble         a = normCV $ CV KDouble    (CDouble   (fromInteger (toInteger a)))
mkConstCV k@(KFP eb sb)   a = normCV $ CV k          (CFP       (fpFromInteger eb sb (toInteger a)))
mkConstCV KRational       a = normCV $ CV KRational  (CRational (fromInteger (toInteger a)))
mkConstCV KChar           a = error $ "Unexpected call to mkConstCV (Char) with value: "   ++ show (toInteger a)
mkConstCV KString         a = error $ "Unexpected call to mkConstCV (String) with value: " ++ show (toInteger a)
mkConstCV (KApp s _)      a = error $ "Unexpected call to mkConstCV with kind: " ++ s ++ " with value: " ++ show (toInteger a)
mkConstCV (KADT s _ _)    a = error $ "Unexpected call to mkConstCV with ADT: "  ++ s ++ " with value: " ++ show (toInteger a)
mkConstCV k@KList{}       a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KSet{}        a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KTuple{}      a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KArray{}      a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)

-- | Generate a random constant value ('CVal') of the correct kind. We error out for a completely uninterpreted type.
randomCVal :: Kind -> IO CVal
randomCVal k =
  case k of
    KVar{}             -> error $ "randomCVal: Unexpected kind: " ++ show k
    KBool              -> CInteger  <$> randomRIO (0, 1)
    KBounded s w       -> CInteger  <$> randomRIO (bounds s w)
    KUnbounded         -> CInteger  <$> randomIO
    KReal              -> CAlgReal  <$> randomIO
    KFloat             -> CFloat    <$> randomIO
    KDouble            -> CDouble   <$> randomIO
    KRational          -> CRational <$> randomIO

    -- Rather bad, but OK
    KFP eb sb          -> do sgn <- randomRIO (0 :: Integer, 1)
                             let sign = sgn == 1
                             e   <- randomRIO (0 :: Integer, 2^eb-1)
                             s   <- randomRIO (0 :: Integer, 2^sb-1)
                             pure $ CFP $ fpFromRawRep sign (e, eb) (s, sb)

    -- TODO: KString/KChar currently only go for 0..255; include unicode?
    KString            -> do l <- randomRIO (0, 100)
                             CString <$> replicateM l (chr <$> randomRIO (0, 255))
    KChar              -> CChar . chr <$> randomRIO (0, 255)

    -- TODO: Can we do something here?
    KApp s _           -> error $ "randomCVal: Not supported for KApp: " ++ s

    KADT _ _ cstrs@(_:_) -> do i <- randomRIO (0, length cstrs - 1)
                               let (c, fks) = cstrs !! i
                               vs <- mapM randomCVal fks
                               pure $ CADT (c, zip fks vs)
    KADT s _ _         -> error $ "randomCVal: Not supported for ADT:  " ++ s

    KList ek           -> do l <- randomRIO (0, 100)
                             CList <$> replicateM l (randomCVal ek)

    KSet  ek           -> do i <- randomIO                           -- regular or complement
                             l <- randomRIO (0, 100)                 -- some set upto 100 elements
                             vals <- Set.fromList <$> replicateM l (randomCVal ek)
                             return $ CSet $ if i then RegularSet vals else ComplementSet vals

    KTuple ks          -> CTuple <$> traverse randomCVal ks

    KArray k1 k2       -> do l   <- randomRIO (0, 100)
                             ks  <- replicateM l (randomCVal k1)
                             vs  <- replicateM l (randomCVal k2)
                             def <- randomCVal k2
                             return $ CArray $ ArrayModel (zip ks vs) def
  where
    bounds :: Bool -> Int -> (Integer, Integer)
    bounds False w = (0, 2^w - 1)
    bounds True  w = (-x, x-1) where x = 2^(w-1)

-- | Generate a random constant value (i.e., t'CV') of the correct kind.
randomCV :: Kind -> IO CV
randomCV k = CV k <$> randomCVal k

{- HLint ignore module "Redundant if" -}
