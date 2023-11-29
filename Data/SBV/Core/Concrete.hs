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

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE Rank2Types          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.Concrete where

import Control.Monad (replicateM)

import Data.Bits
import System.Random (randomIO, randomRIO)

import Data.Char (chr, isSpace)
import Data.List (intercalate)

import Data.SBV.Core.Kind
import Data.SBV.Core.AlgReals
import Data.SBV.Core.SizedFloats

import Data.Proxy

import Data.SBV.Utils.Numeric (fpIsEqualObjectH, fpCompareObjectH)

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Generics as G

-- | A 'RCSet' is either a regular set or a set given by its complement from the corresponding universal set.
data RCSet a = RegularSet    (Set a)
             | ComplementSet (Set a)
             deriving G.Data

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

-- | A constant value
data CVal = CAlgReal  !AlgReal             -- ^ Algebraic real
          | CInteger  !Integer             -- ^ Bit-vector/unbounded integer
          | CFloat    !Float               -- ^ Float
          | CDouble   !Double              -- ^ Double
          | CFP       !FP                  -- ^ Arbitrary float
          | CRational Rational             -- ^ Rational
          | CChar     !Char                -- ^ Character
          | CString   !String              -- ^ String
          | CList     ![CVal]              -- ^ List
          | CSet      !(RCSet CVal)        -- ^ Set. Can be regular or complemented.
          | CUserSort !(Maybe Int, String) -- ^ Value of an uninterpreted/user kind. The Maybe Int shows index position for enumerations
          | CTuple    ![CVal]              -- ^ Tuple
          | CMaybe    !(Maybe CVal)        -- ^ Maybe
          | CEither   !(Either CVal CVal)  -- ^ Disjoint union
          deriving G.Data

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
cvRank CUserSort {} = 10
cvRank CTuple    {} = 11
cvRank CMaybe    {} = 12
cvRank CEither   {} = 13

-- | Eq instance for CVVal. Note that we cannot simply derive Eq/Ord, since CVAlgReal doesn't have proper
-- instances for these when values are infinitely precise reals. However, we do
-- need a structural eq/ord for Map indexes; so define custom ones here:
instance Eq CVal where
  CAlgReal  a == CAlgReal  b = a `algRealStructuralEqual` b
  CInteger  a == CInteger  b = a == b
  CFloat    a == CFloat    b = a `fpIsEqualObjectH` b   -- We don't want +0/-0 to be confused; and also we want NaN = NaN here!
  CDouble   a == CDouble   b = a `fpIsEqualObjectH` b   -- ditto
  CRational a == CRational b = a == b
  CChar     a == CChar     b = a == b
  CString   a == CString   b = a == b
  CList     a == CList     b = a == b
  CSet      a == CSet      b = a `eqRCSet` b
  CUserSort a == CUserSort b = a == b
  CTuple    a == CTuple    b = a == b
  CMaybe    a == CMaybe    b = a == b
  CEither   a == CEither   b = a == b
  a           == b           = if cvRank a == cvRank b
                                  then error $ unlines [ ""
                                                       , "*** Data.SBV.Eq.CVal: Impossible happened: same rank in comparison fallthru"
                                                       , "***"
                                                       , "***   Received: " ++ show (cvRank a, cvRank b)
                                                       , "***"
                                                       , "*** Please report this as a bug!"
                                                       ]
                                  else False

-- | Ord instance for VWVal. Same comments as the 'Eq' instance why this cannot be derived.
instance Ord CVal where
  CAlgReal  a `compare` CAlgReal  b = a `algRealStructuralCompare` b
  CInteger  a `compare` CInteger  b = a `compare`                  b
  CFloat    a `compare` CFloat    b = a `fpCompareObjectH`         b
  CDouble   a `compare` CDouble   b = a `fpCompareObjectH`         b
  CRational a `compare` CRational b = a `compare`                  b
  CFP       a `compare` CFP       b = a `fprCompareObject`         b
  CChar     a `compare` CChar     b = a `compare`                  b
  CString   a `compare` CString   b = a `compare`                  b
  CList     a `compare` CList     b = a `compare`                  b
  CSet      a `compare` CSet      b = a `compareRCSet`             b
  CUserSort a `compare` CUserSort b = a `compare`                  b
  CTuple    a `compare` CTuple    b = a `compare`                  b
  CMaybe    a `compare` CMaybe    b = a `compare`                  b
  CEither   a `compare` CEither   b = a `compare`                  b
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

-- | 'CV' represents a concrete word of a fixed size:
-- For signed words, the most significant digit is considered to be the sign.
data CV = CV { _cvKind  :: !Kind
             , cvVal    :: !CVal
             }
             deriving (Eq, Ord, G.Data)

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
                                       | isInterval = v ++ " :: [" ++ showBaseKind (kindOf extCV) ++ "]"
                                       | True       = v ++ " :: "  ++ showBaseKind (kindOf extCV)

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

-- | Constant False as a 'CV'. We represent it using the integer value 0.
falseCV :: CV
falseCV = CV KBool (CInteger 0)

-- | Constant True as a 'CV'. We represent it using the integer value 1.
trueCV :: CV
trueCV  = CV KBool (CInteger 1)

-- | Lift a unary function through a 'CV'.
liftCV :: (AlgReal             -> b)
       -> (Integer             -> b)
       -> (Float               -> b)
       -> (Double              -> b)
       -> (FP                  -> b)
       -> (Rational            -> b)
       -> (Char                -> b)
       -> (String              -> b)
       -> ((Maybe Int, String) -> b)
       -> ([CVal]              -> b)
       -> (RCSet CVal          -> b)
       -> ([CVal]              -> b)
       -> (Maybe CVal          -> b)
       -> (Either CVal CVal    -> b)
       -> CV
       -> b
liftCV f _ _ _ _ _ _ _ _ _ _ _ _ _ (CV _ (CAlgReal  v)) = f v
liftCV _ f _ _ _ _ _ _ _ _ _ _ _ _ (CV _ (CInteger  v)) = f v
liftCV _ _ f _ _ _ _ _ _ _ _ _ _ _ (CV _ (CFloat    v)) = f v
liftCV _ _ _ f _ _ _ _ _ _ _ _ _ _ (CV _ (CDouble   v)) = f v
liftCV _ _ _ _ f _ _ _ _ _ _ _ _ _ (CV _ (CFP       v)) = f v
liftCV _ _ _ _ _ f _ _ _ _ _ _ _ _ (CV _ (CRational v)) = f v
liftCV _ _ _ _ _ _ f _ _ _ _ _ _ _ (CV _ (CChar     v)) = f v
liftCV _ _ _ _ _ _ _ f _ _ _ _ _ _ (CV _ (CString   v)) = f v
liftCV _ _ _ _ _ _ _ _ f _ _ _ _ _ (CV _ (CUserSort v)) = f v
liftCV _ _ _ _ _ _ _ _ _ f _ _ _ _ (CV _ (CList     v)) = f v
liftCV _ _ _ _ _ _ _ _ _ _ f _ _ _ (CV _ (CSet      v)) = f v
liftCV _ _ _ _ _ _ _ _ _ _ _ f _ _ (CV _ (CTuple    v)) = f v
liftCV _ _ _ _ _ _ _ _ _ _ _ _ f _ (CV _ (CMaybe    v)) = f v
liftCV _ _ _ _ _ _ _ _ _ _ _ _ _ f (CV _ (CEither   v)) = f v

-- | Lift a binary function through a 'CV'.
liftCV2 :: (AlgReal             -> AlgReal             -> b)
        -> (Integer             -> Integer             -> b)
        -> (Float               -> Float               -> b)
        -> (Double              -> Double              -> b)
        -> (FP                  -> FP                  -> b)
        -> (Rational            -> Rational            -> b)
        -> (Char                -> Char                -> b)
        -> (String              -> String              -> b)
        -> ([CVal]              -> [CVal]              -> b)
        -> ([CVal]              -> [CVal]              -> b)
        -> (Maybe CVal          -> Maybe CVal          -> b)
        -> (Either CVal CVal    -> Either CVal CVal    -> b)
        -> ((Maybe Int, String) -> (Maybe Int, String) -> b)
        -> CV                   -> CV                  -> b
liftCV2 r i f d af ra c s u v m e w x y = case (cvVal x, cvVal y) of
                                           (CAlgReal   a, CAlgReal   b) -> r  a b
                                           (CInteger   a, CInteger   b) -> i  a b
                                           (CFloat     a, CFloat     b) -> f  a b
                                           (CDouble    a, CDouble    b) -> d  a b
                                           (CFP        a, CFP        b) -> af a b
                                           (CRational  a, CRational  b) -> ra a b
                                           (CChar      a, CChar      b) -> c  a b
                                           (CString    a, CString    b) -> s  a b
                                           (CList      a, CList      b) -> u  a b
                                           (CTuple     a, CTuple     b) -> v  a b
                                           (CMaybe     a, CMaybe     b) -> m  a b
                                           (CEither    a, CEither    b) -> e  a b
                                           (CUserSort  a, CUserSort  b) -> w  a b
                                           _                            -> error $ "SBV.liftCV2: impossible, incompatible args received: " ++ show (x, y)

-- | Map a unary function through a 'CV'.
mapCV :: (AlgReal             -> AlgReal)
      -> (Integer             -> Integer)
      -> (Float               -> Float)
      -> (Double              -> Double)
      -> (FP                  -> FP)
      -> (Rational            -> Rational)
      -> (Char                -> Char)
      -> (String              -> String)
      -> ((Maybe Int, String) -> (Maybe Int, String))
      -> CV
      -> CV
mapCV r i f d af ra c s u x  = normCV $ CV (kindOf x) $ case cvVal x of
                                                          CAlgReal  a -> CAlgReal  (r  a)
                                                          CInteger  a -> CInteger  (i  a)
                                                          CFloat    a -> CFloat    (f  a)
                                                          CDouble   a -> CDouble   (d  a)
                                                          CFP       a -> CFP       (af a)
                                                          CRational a -> CRational (ra a)
                                                          CChar     a -> CChar     (c  a)
                                                          CString   a -> CString   (s  a)
                                                          CUserSort a -> CUserSort (u  a)
                                                          CList{}     -> error "Data.SBV.mapCV: Unexpected call through mapCV with lists!"
                                                          CSet{}      -> error "Data.SBV.mapCV: Unexpected call through mapCV with sets!"
                                                          CTuple{}    -> error "Data.SBV.mapCV: Unexpected call through mapCV with tuples!"
                                                          CMaybe{}    -> error "Data.SBV.mapCV: Unexpected call through mapCV with maybe!"
                                                          CEither{}   -> error "Data.SBV.mapCV: Unexpected call through mapCV with either!"

-- | Map a binary function through a 'CV'.
mapCV2 :: (AlgReal             -> AlgReal             -> AlgReal)
       -> (Integer             -> Integer             -> Integer)
       -> (Float               -> Float               -> Float)
       -> (Double              -> Double              -> Double)
       -> (FP                  -> FP                  -> FP)
       -> (Rational            -> Rational            -> Rational)
       -> (Char                -> Char                -> Char)
       -> (String              -> String              -> String)
       -> ((Maybe Int, String) -> (Maybe Int, String) -> (Maybe Int, String))
       -> CV
       -> CV
       -> CV
mapCV2 r i f d af ra c s u x y = case (cvSameType x y, cvVal x, cvVal y) of
                                  (True, CAlgReal  a, CAlgReal  b) -> normCV $ CV (kindOf x) (CAlgReal  (r  a b))
                                  (True, CInteger  a, CInteger  b) -> normCV $ CV (kindOf x) (CInteger  (i  a b))
                                  (True, CFloat    a, CFloat    b) -> normCV $ CV (kindOf x) (CFloat    (f  a b))
                                  (True, CDouble   a, CDouble   b) -> normCV $ CV (kindOf x) (CDouble   (d  a b))
                                  (True, CFP       a, CFP       b) -> normCV $ CV (kindOf x) (CFP       (af a b))
                                  (True, CRational a, CRational b) -> normCV $ CV (kindOf x) (CRational (ra a b))
                                  (True, CChar     a, CChar     b) -> normCV $ CV (kindOf x) (CChar     (c  a b))
                                  (True, CString   a, CString   b) -> normCV $ CV (kindOf x) (CString   (s  a b))
                                  (True, CUserSort a, CUserSort b) -> normCV $ CV (kindOf x) (CUserSort (u  a b))
                                  (True, CList{},     CList{})     -> error "Data.SBV.mapCV2: Unexpected call through mapCV2 with lists!"
                                  (True, CTuple{},    CTuple{})    -> error "Data.SBV.mapCV2: Unexpected call through mapCV2 with tuples!"
                                  (True, CMaybe{},    CMaybe{})    -> error "Data.SBV.mapCV2: Unexpected call through mapCV2 with maybes!"
                                  (True, CEither{},   CEither{})   -> error "Data.SBV.mapCV2: Unexpected call through mapCV2 with eithers!"
                                  _                                -> error $ "Data.SBV.mapCV2: impossible, incompatible args received: " ++ show (x, y)

-- | Show instance for 'CV'.
instance Show CV where
  show = showCV True

-- | Show instance for Generalized 'CV'
instance Show GeneralizedCV where
  show (ExtendedCV k) = showExtCV True k
  show (RegularCV  c) = showCV    True c

-- | Show a CV, with kind info if bool is True
showCV :: Bool -> CV -> String
showCV shk w | isBoolean w = show (cvToBool w) ++ (if shk then " :: Bool" else "")
showCV shk w               = liftCV show show show show show show show show snd shL shS shT shMaybe shEither w ++ kInfo
      where kw = kindOf w

            kInfo | shk  = " :: " ++ showBaseKind kw
                  | True = ""

            shL xs = "[" ++ intercalate "," (map (showCV False . CV ke) xs) ++ "]"
              where ke = case kw of
                           KList k -> k
                           _       -> error $ "Data.SBV.showCV: Impossible happened, expected list, got: " ++ show kw

            -- we represent complements as @U - set@. This might be confusing, but is utterly cute!
            shS :: RCSet CVal -> String
            shS eru = case eru of
                        RegularSet    e              -> sh e
                        ComplementSet e | Set.null e -> "U"
                                        | True       -> "U - " ++ sh e
              where sh xs = "{" ++ intercalate "," (map (showCV False . CV ke) (Set.toList xs)) ++ "}"
                    ke = case kw of
                           KSet k -> k
                           _      -> error $ "Data.SBV.showCV: Impossible happened, expected set, got: " ++ show kw

            shT :: [CVal] -> String
            shT xs = "(" ++ intercalate "," xs' ++ ")"
              where xs' = case kw of
                            KTuple ks | length ks == length xs -> zipWith (\k x -> showCV False (CV k x)) ks xs
                            _   -> error $ "Data.SBV.showCV: Impossible happened, expected tuple (of length " ++ show (length xs) ++ "), got: " ++ show kw

            shMaybe :: Maybe CVal -> String
            shMaybe c = case (c, kw) of
                          (Nothing, KMaybe{}) -> "Nothing"
                          (Just x,  KMaybe k) -> "Just " ++ paren (showCV False (CV k x))
                          _                   -> error $ "Data.SBV.showCV: Impossible happened, expected maybe, got: " ++ show kw

            shEither :: Either CVal CVal -> String
            shEither val
              | KEither k1 k2 <- kw = case val of
                                        Left  x -> "Left "  ++ paren (showCV False (CV k1 x))
                                        Right y -> "Right " ++ paren (showCV False (CV k2 y))
              | True                = error $ "Data.SBV.showCV: Impossible happened, expected sum, got: " ++ show kw

            -- kind of crude, but works ok
            paren v
              | needsParen = '(' : v ++ ")"
              | True       = v
              where needsParen = case dropWhile isSpace v of
                                   []         -> False
                                   rest@(x:_) -> x == '-' || (any isSpace rest && x `notElem` "{[(")

-- | Create a constant word from an integral.
mkConstCV :: Integral a => Kind -> a -> CV
mkConstCV KBool           a = normCV $ CV KBool      (CInteger  (toInteger a))
mkConstCV k@KBounded{}    a = normCV $ CV k          (CInteger  (toInteger a))
mkConstCV KUnbounded      a = normCV $ CV KUnbounded (CInteger  (toInteger a))
mkConstCV KReal           a = normCV $ CV KReal      (CAlgReal  (fromInteger (toInteger a)))
mkConstCV KFloat          a = normCV $ CV KFloat     (CFloat    (fromInteger (toInteger a)))
mkConstCV KDouble         a = normCV $ CV KDouble    (CDouble   (fromInteger (toInteger a)))
mkConstCV k@KFP{}         a = normCV $ CV k          (CFP       (fromInteger (toInteger a)))
mkConstCV KRational       a = normCV $ CV KRational  (CRational (fromInteger (toInteger a)))
mkConstCV KChar           a = error $ "Unexpected call to mkConstCV (Char) with value: "   ++ show (toInteger a)
mkConstCV KString         a = error $ "Unexpected call to mkConstCV (String) with value: " ++ show (toInteger a)
mkConstCV (KUserSort s _) a = error $ "Unexpected call to mkConstCV with user kind: " ++ s ++ " with value: " ++ show (toInteger a)
mkConstCV k@KList{}       a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KSet{}        a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KTuple{}      a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KMaybe{}      a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)
mkConstCV k@KEither{}     a = error $ "Unexpected call to mkConstCV (" ++ show k ++ ") with value: " ++ show (toInteger a)

-- | Generate a random constant value ('CVal') of the correct kind.
randomCVal :: Kind -> IO CVal
randomCVal k =
  case k of
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
    KUserSort s _      -> error $ "Unexpected call to randomCVal with user kind: " ++ s
    KList ek           -> do l <- randomRIO (0, 100)
                             CList <$> replicateM l (randomCVal ek)
    KSet  ek           -> do i <- randomIO                           -- regular or complement
                             l <- randomRIO (0, 100)                 -- some set upto 100 elements
                             vals <- Set.fromList <$> replicateM l (randomCVal ek)
                             return $ CSet $ if i then RegularSet vals else ComplementSet vals
    KTuple ks          -> CTuple <$> traverse randomCVal ks
    KMaybe ke          -> do i <- randomIO
                             if i
                                then return $ CMaybe Nothing
                                else CMaybe . Just <$> randomCVal ke
    KEither k1 k2      -> do i <- randomIO
                             if i
                                then CEither . Left  <$> randomCVal k1
                                else CEither . Right <$> randomCVal k2
  where
    bounds :: Bool -> Int -> (Integer, Integer)
    bounds False w = (0, 2^w - 1)
    bounds True  w = (-x, x-1) where x = 2^(w-1)

-- | Generate a random constant value ('CV') of the correct kind.
randomCV :: Kind -> IO CV
randomCV k = CV k <$> randomCVal k

{- HLint ignore module "Redundant if" -}
