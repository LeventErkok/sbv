-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Concrete
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Operations on concrete values
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.Concrete
  ( module Data.SBV.BitVectors.Concrete
  ) where

import Data.Bits
import System.Random (randomIO, randomRIO)

import Data.SBV.BitVectors.Kind
import Data.SBV.BitVectors.AlgReals

-- | A constant value
data CWVal = CWAlgReal  !AlgReal              -- ^ algebraic real
           | CWInteger  !Integer              -- ^ bit-vector/unbounded integer
           | CWFloat    !Float                -- ^ float
           | CWDouble   !Double               -- ^ double
           | CWUserSort !(Maybe Int, String)  -- ^ value of an uninterpreted/user kind. The Maybe Int shows index position for enumerations

-- | Eq instance for CWVal. Note that we cannot simply derive Eq/Ord, since CWAlgReal doesn't have proper
-- instances for these when values are infinitely precise reals. However, we do
-- need a structural eq/ord for Map indexes; so define custom ones here:
instance Eq CWVal where
  CWAlgReal a  == CWAlgReal b       = a `algRealStructuralEqual` b
  CWInteger a  == CWInteger b       = a == b
  CWUserSort a == CWUserSort b = a == b
  CWFloat a    == CWFloat b         = a == b
  CWDouble a   == CWDouble b        = a == b
  _            == _                 = False

-- | Ord instance for CWVal. Same comments as the 'Eq' instance why this cannot be derived.
instance Ord CWVal where
  CWAlgReal a `compare` CWAlgReal b   = a `algRealStructuralCompare` b
  CWAlgReal _ `compare` CWInteger _   = LT
  CWAlgReal _ `compare` CWFloat _     = LT
  CWAlgReal _ `compare` CWDouble _    = LT
  CWAlgReal _ `compare` CWUserSort _  = LT

  CWInteger _ `compare` CWAlgReal _   = GT
  CWInteger a `compare` CWInteger b   = a `compare` b
  CWInteger _ `compare` CWFloat _     = LT
  CWInteger _ `compare` CWDouble _    = LT
  CWInteger _ `compare` CWUserSort _  = LT

  CWFloat _   `compare` CWAlgReal _   = GT
  CWFloat _   `compare` CWInteger _   = GT
  CWFloat a   `compare` CWFloat b     = a `compare` b
  CWFloat _   `compare` CWDouble _    = LT
  CWFloat _   `compare` CWUserSort _  = LT

  CWDouble _  `compare` CWAlgReal _   = GT
  CWDouble _  `compare` CWInteger _   = GT
  CWDouble _  `compare` CWFloat _     = GT
  CWDouble a  `compare` CWDouble b    = a `compare` b
  CWDouble _  `compare` CWUserSort _  = LT

  CWUserSort _ `compare` CWAlgReal _  = GT
  CWUserSort _ `compare` CWInteger _  = GT
  CWUserSort _ `compare` CWFloat _    = GT
  CWUserSort _ `compare` CWDouble _   = GT
  CWUserSort a `compare` CWUserSort b = a `compare` b

-- | 'CW' represents a concrete word of a fixed size:
-- Endianness is mostly irrelevant (see the 'FromBits' class).
-- For signed words, the most significant digit is considered to be the sign.
data CW = CW { _cwKind  :: !Kind
             , cwVal    :: !CWVal
             }
        deriving (Eq, Ord)

-- | 'Kind' instance for CW
instance HasKind CW where
  kindOf (CW k _) = k

-- | Are two CW's of the same type?
cwSameType :: CW -> CW -> Bool
cwSameType x y = kindOf x == kindOf y

-- | Convert a CW to a Haskell boolean (NB. Assumes input is well-kinded)
cwToBool :: CW -> Bool
cwToBool x = cwVal x /= CWInteger 0

-- | Normalize a CW. Essentially performs modular arithmetic to make sure the
-- value can fit in the given bit-size. Note that this is rather tricky for
-- negative values, due to asymmetry. (i.e., an 8-bit negative number represents
-- values in the range -128 to 127; thus we have to be careful on the negative side.)
normCW :: CW -> CW
normCW c@(CW (KBounded signed sz) (CWInteger v)) = c { cwVal = CWInteger norm }
 where norm | sz == 0 = 0
            | signed  = let rg = 2 ^ (sz - 1)
                        in case divMod v rg of
                                  (a, b) | even a -> b
                                  (_, b)          -> b - rg
            | True    = v `mod` (2 ^ sz)
normCW c@(CW KBool (CWInteger v)) = c { cwVal = CWInteger (v .&. 1) }
normCW c = c

-- | Constant False as a CW. We represent it using the integer value 0.
falseCW :: CW
falseCW = CW KBool (CWInteger 0)

-- | Constant True as a CW. We represent it using the integer value 1.
trueCW :: CW
trueCW  = CW KBool (CWInteger 1)

-- | Lift a unary function thruough a CW
liftCW :: (AlgReal -> b) -> (Integer -> b) -> (Float -> b) -> (Double -> b) -> ((Maybe Int, String) -> b) -> CW -> b
liftCW f _ _ _ _ (CW _ (CWAlgReal v))  = f v
liftCW _ f _ _ _ (CW _ (CWInteger v))  = f v
liftCW _ _ f _ _ (CW _ (CWFloat v))    = f v
liftCW _ _ _ f _ (CW _ (CWDouble v))   = f v
liftCW _ _ _ _ f (CW _ (CWUserSort v)) = f v

-- | Lift a binary function through a CW
liftCW2 :: (AlgReal -> AlgReal -> b) -> (Integer -> Integer -> b) -> (Float -> Float -> b) -> (Double -> Double -> b) -> ((Maybe Int, String) -> (Maybe Int, String) -> b) -> CW -> CW -> b
liftCW2 r i f d u x y = case (cwVal x, cwVal y) of
                         (CWAlgReal a,  CWAlgReal b)  -> r a b
                         (CWInteger a,  CWInteger b)  -> i a b
                         (CWFloat a,    CWFloat b)    -> f a b
                         (CWDouble a,   CWDouble b)   -> d a b
                         (CWUserSort a, CWUserSort b) -> u a b
                         _                            -> error $ "SBV.liftCW2: impossible, incompatible args received: " ++ show (x, y)

-- | Map a unary function through a CW.
mapCW :: (AlgReal -> AlgReal) -> (Integer -> Integer) -> (Float -> Float) -> (Double -> Double) -> ((Maybe Int, String) -> (Maybe Int, String)) -> CW -> CW
mapCW r i f d u x  = normCW $ CW (kindOf x) $ case cwVal x of
                                               CWAlgReal a  -> CWAlgReal  (r a)
                                               CWInteger a  -> CWInteger  (i a)
                                               CWFloat a    -> CWFloat    (f a)
                                               CWDouble a   -> CWDouble   (d a)
                                               CWUserSort a -> CWUserSort (u a)

-- | Map a binary function through a CW.
mapCW2 :: (AlgReal -> AlgReal -> AlgReal) -> (Integer -> Integer -> Integer) -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> ((Maybe Int, String) -> (Maybe Int, String) -> (Maybe Int, String)) -> CW -> CW -> CW
mapCW2 r i f d u x y = case (cwSameType x y, cwVal x, cwVal y) of
                        (True, CWAlgReal a,  CWAlgReal b)  -> normCW $ CW (kindOf x) (CWAlgReal  (r a b))
                        (True, CWInteger a,  CWInteger b)  -> normCW $ CW (kindOf x) (CWInteger  (i a b))
                        (True, CWFloat a,    CWFloat b)    -> normCW $ CW (kindOf x) (CWFloat    (f a b))
                        (True, CWDouble a,   CWDouble b)   -> normCW $ CW (kindOf x) (CWDouble   (d a b))
                        (True, CWUserSort a, CWUserSort b) -> normCW $ CW (kindOf x) (CWUserSort (u a b))
                        _                                  -> error $ "SBV.mapCW2: impossible, incompatible args received: " ++ show (x, y)

-- | Show instance for 'CW'.
instance Show CW where
  show = showCW True

-- | Show a CW, with kind info if bool is True
showCW :: Bool -> CW -> String
showCW shk w | isBoolean w = show (cwToBool w) ++ (if shk then " :: Bool" else "")
showCW shk w               = liftCW show show show show snd w ++ kInfo
      where kInfo | shk  = " :: " ++ shKind (kindOf w)
                  | True = ""
            shKind k@KUserSort {}         = show k
            shKind k | ('S':sk) <- show k = sk
            shKind k                      = show k

-- | Create a constant word from an integral.
mkConstCW :: Integral a => Kind -> a -> CW
mkConstCW KBool           a = normCW $ CW KBool      (CWInteger (toInteger a))
mkConstCW k@KBounded{}    a = normCW $ CW k          (CWInteger (toInteger a))
mkConstCW KUnbounded      a = normCW $ CW KUnbounded (CWInteger (toInteger a))
mkConstCW KReal           a = normCW $ CW KReal      (CWAlgReal (fromInteger (toInteger a)))
mkConstCW KFloat          a = normCW $ CW KFloat     (CWFloat   (fromInteger (toInteger a)))
mkConstCW KDouble         a = normCW $ CW KDouble    (CWDouble  (fromInteger (toInteger a)))
mkConstCW (KUserSort s _) a = error $ "Unexpected call to mkConstCW with uninterpreted kind: " ++ s ++ " with value: " ++ show (toInteger a)

-- | Generate a random constant value ('CWVal') of the correct kind.
randomCWVal :: Kind -> IO CWVal
randomCWVal k =
  case k of
    KBool         -> fmap CWInteger (randomRIO (0,1))
    KBounded s w  -> fmap CWInteger (randomRIO (bounds s w))
    KUnbounded    -> fmap CWInteger randomIO
    KReal         -> fmap CWAlgReal randomIO
    KFloat        -> fmap CWFloat randomIO
    KDouble       -> fmap CWDouble randomIO
    KUserSort s _ -> error $ "Unexpected call to randomCWVal with uninterpreted kind: " ++ s
  where
    bounds :: Bool -> Int -> (Integer, Integer)
    bounds False w = (0, 2^w - 1)
    bounds True w = (-x, x-1) where x = 2^(w-1)

-- | Generate a random constant value ('CW') of the correct kind.
randomCW :: Kind -> IO CW
randomCW k = fmap (CW k) (randomCWVal k)
