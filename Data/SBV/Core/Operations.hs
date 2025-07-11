-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Operations
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Constructors and basic operations on symbolic values
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.Operations
  (
  -- ** Basic constructors
    svTrue, svFalse, svBool
  , svInteger, svFloat, svDouble, svFloatingPoint, svReal, svEnumFromThenTo, svString, svChar
  -- ** Basic destructors
  , svAsBool, svAsInteger, svNumerator, svDenominator
  -- ** Basic operations
  , svPlus, svTimes, svMinus, svUNeg, svAbs, svSignum
  , svDivide, svQuot, svRem, svQuotRem, svDivides
  , svEqual, svNotEqual, svStrongEqual, svImplies
  , svLessThan, svGreaterThan, svLessEq, svGreaterEq, svStructuralLessThan
  , svAnd, svOr, svXOr, svNot
  , svShl, svShr, svRol, svRor
  , svExtract, svJoin, svZeroExtend, svSignExtend
  , svIte, svLazyIte, svSymbolicMerge
  , svSelect
  , svSign, svUnsign, svSetBit, svWordFromBE, svWordFromLE
  , svExp, svFromIntegral
  -- ** Overflows
  , svMkOverflow1, svMkOverflow2
  -- ** Derived operations
  , svToWord1, svFromWord1, svTestBit
  , svShiftLeft, svShiftRight
  , svRotateLeft, svRotateRight
  , svBarrelRotateLeft, svBarrelRotateRight
  , svBlastLE, svBlastBE
  , svAddConstant, svIncrement, svDecrement
  , svFloatAsSWord32, svDoubleAsSWord64, svFloatingPointAsSWord
  -- Utils
  , mkSymOp
  )
  where

import Prelude hiding (Foldable(..))
import Data.Bits (Bits(..))
import Data.List (genericIndex, genericLength, genericTake, foldr, length, foldl', elem, nub, sort)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic
import Data.SBV.Core.SizedFloats

import Data.Ratio

import Data.SBV.Utils.Numeric (fpIsEqualObjectH, floatToWord, doubleToWord)

import LibBF

--------------------------------------------------------------------------------
-- Basic constructors

-- | Boolean True.
svTrue :: SVal
svTrue = SVal KBool (Left trueCV)

-- | Boolean False.
svFalse :: SVal
svFalse = SVal KBool (Left falseCV)

-- | Convert from a Boolean.
svBool :: Bool -> SVal
svBool b = if b then svTrue else svFalse

-- | Convert from an Integer.
svInteger :: Kind -> Integer -> SVal
svInteger k n = SVal k (Left $! mkConstCV k n)

-- | Convert from a Float
svFloat :: Float -> SVal
svFloat f = SVal KFloat (Left $! CV KFloat (CFloat f))

-- | Convert from a Double
svDouble :: Double -> SVal
svDouble d = SVal KDouble (Left $! CV KDouble (CDouble d))

-- | Convert from a generalized floating point
svFloatingPoint :: FP -> SVal
svFloatingPoint f@(FP eb sb _) = SVal k (Left $! CV k (CFP f))
  where k  = KFP eb sb

-- | Convert from a String
svString :: String -> SVal
svString s = SVal KString (Left $! CV KString (CString s))

-- | Convert from a Char
svChar :: Char -> SVal
svChar c = SVal KChar (Left $! CV KChar (CChar c))

-- | Convert from a Rational
svReal :: Rational -> SVal
svReal d = SVal KReal (Left $! CV KReal (CAlgReal (fromRational d)))

--------------------------------------------------------------------------------
-- Basic destructors

-- | Extract a bool, by properly interpreting the integer stored.
svAsBool :: SVal -> Maybe Bool
svAsBool (SVal _ (Left cv)) = Just (cvToBool cv)
svAsBool _                  = Nothing

-- | Extract an integer from a concrete value.
svAsInteger :: SVal -> Maybe Integer
svAsInteger (SVal _ (Left (CV _ (CInteger n)))) = Just n
svAsInteger _                                   = Nothing

-- | Grab the numerator of an SReal, if available
svNumerator :: SVal -> Maybe Integer
svNumerator (SVal KReal (Left (CV KReal (CAlgReal (AlgRational True r))))) = Just $ numerator r
svNumerator _                                                              = Nothing

-- | Grab the denominator of an SReal, if available
svDenominator :: SVal -> Maybe Integer
svDenominator (SVal KReal (Left (CV KReal (CAlgReal (AlgRational True r))))) = Just $ denominator r
svDenominator _                                                              = Nothing

-------------------------------------------------------------------------------------
-- | Constructing [x, y, .. z] and [x .. y]. Only works when all arguments are concrete and integral and the result is guaranteed finite
-- Note that the it isn't "obviously" clear why the following works; after all we're doing the construction over Integer's and mapping
-- it back to other types such as SIntN/SWordN. The reason is that the values we receive are guaranteed to be in their domains; and thus
-- the lifting to Integers preserves the bounds; and then going back is just fine. So, things like @[1, 5 .. 200] :: [SInt8]@ work just
-- fine (end evaluate to empty list), since we see @[1, 5 .. -56]@ in the @Integer@ domain. Also note the explicit check for @s /= f@
-- below to make sure we don't stutter and produce an infinite list.
svEnumFromThenTo :: SVal -> Maybe SVal -> SVal -> Maybe [SVal]
svEnumFromThenTo bf mbs bt
  | Just bs <- mbs, Just f <- svAsInteger bf, Just s <- svAsInteger bs, Just t <- svAsInteger bt, s /= f = Just $ map (svInteger (kindOf bf)) [f, s .. t]
  | Nothing <- mbs, Just f <- svAsInteger bf,                           Just t <- svAsInteger bt         = Just $ map (svInteger (kindOf bf)) [f    .. t]
  | True                                                                                                 = Nothing

-------------------------------------------------------------------------------------
-- Basic operations

-- | Addition.
svPlus :: SVal -> SVal -> SVal
svPlus x y
  | isConcreteZero x = y
  | isConcreteZero y = x
  | True             = liftSym2 (mkSymOp Plus) [rationalCheck] (+) (+) (+) (+) (+) (+) x y

-- | Multiplication.
svTimes :: SVal -> SVal -> SVal
svTimes x y
  | isConcreteZero x = x
  | isConcreteZero y = y
  | isConcreteOne x  = y
  | isConcreteOne y  = x
  | True             = liftSym2 (mkSymOp Times) [rationalCheck] (*) (*) (*) (*) (*) (*) x y

-- | Subtraction.
svMinus :: SVal -> SVal -> SVal
svMinus x y
  | isConcreteZero y = x
  | True             = liftSym2 (mkSymOp Minus) [rationalCheck] (-) (-) (-) (-) (-) (-) x y

-- | Unary minus. We handle arbitrary-FP's specially here, just for the negated literals.
svUNeg :: SVal -> SVal
svUNeg = liftSym1 (mkSymOp1 UNeg) negate negate negate negate negate negate

-- | Absolute value.
svAbs :: SVal -> SVal
svAbs = liftSym1 (mkSymOp1 Abs) abs abs abs abs abs abs

-- | Signum.
--
-- NB. The following "carefully" tests the number for == 0, as Float/Double's NaN and +/-0
-- cases would cause trouble with explicit equality tests.
svSignum :: SVal -> SVal
svSignum a
  | hasSign a = svIte (a `svGreaterThan` z) i
              $ svIte (a `svLessThan`    z) (svUNeg i) a
  | True      = svIte (a `svGreaterThan` z) i a
  where k = kindOf a
        z = SVal k $ Left $ mkConstCV k (0 :: Integer)
        i = SVal k $ Left $ mkConstCV k (1 :: Integer)

-- | Division.
svDivide :: SVal -> SVal -> SVal
svDivide = liftSym2 (mkSymOp Quot) [rationalCheck] (/) idiv (/) (/) (/) (/)
   where idiv x 0 = x
         idiv x y = x `div` y

-- | Divides predicate
svDivides :: Integer -> SVal -> SVal
svDivides n v
  | n <= 0 = error $ "svDivides: The first argument must be a strictly positive number, received: " ++ show n
  | True   = case v of
              SVal KUnbounded (Left (CV KUnbounded (CInteger val))) -> svBool (val `mod` n == 0)
              _                                                     -> SVal KBool $ Right $ cache c
  where c st = do sva <- svToSV st v
                  newExpr st KBool (SBVApp (Divides n) [sva])

-- | Exponentiation.
svExp :: SVal -> SVal -> SVal
svExp b e
  | Just x <- svAsInteger e
  = if x >= 0 then let go n v
                        | n == 0 = one
                        | even n =             go (n `div` 2) (svTimes v v)
                        | True   = svTimes v $ go (n `div` 2) (svTimes v v)
                   in  go x b
              else error $ "svExp: exponentiation: negative exponent: " ++ show x
  | not (isBounded e) || hasSign e
  = error $ "svExp: exponentiation only works with unsigned bounded symbolic exponents, kind: " ++ show (kindOf e)
  | True
  = prod $ zipWith (\use n -> svIte use n one)
                   (svBlastLE e)
                   (iterate (\x -> svTimes x x) b)
  where prod = foldr svTimes one
        one  = svInteger (kindOf b) 1

-- | Bit-blast: Little-endian. Assumes the input is a bit-vector or a floating point type.
svBlastLE :: SVal -> [SVal]
svBlastLE x = map (svTestBit x) [0 .. intSizeOf x - 1]

-- | Set a given bit at index
svSetBit :: SVal -> Int -> SVal
svSetBit x i = x `svOr` svInteger (kindOf x) (bit i :: Integer)

-- | Bit-blast: Big-endian. Assumes the input is a bit-vector or a floating point type.
svBlastBE :: SVal -> [SVal]
svBlastBE = reverse . svBlastLE

-- | Un-bit-blast from big-endian representation to a word of the right size.
-- The input is assumed to be unsigned.
svWordFromLE :: [SVal] -> SVal
svWordFromLE bs = go zero 0 bs
  where zero = svInteger (KBounded False (length bs)) 0
        go !acc _  []     = acc
        go !acc !i (x:xs) = go (svIte x (svSetBit acc i) acc) (i+1) xs

-- | Un-bit-blast from little-endian representation to a word of the right size.
-- The input is assumed to be unsigned.
svWordFromBE :: [SVal] -> SVal
svWordFromBE = svWordFromLE . reverse

-- | Add a constant value:
svAddConstant :: Integral a => SVal -> a -> SVal
svAddConstant x i = x `svPlus` svInteger (kindOf x) (fromIntegral i)

-- | Increment:
svIncrement :: SVal -> SVal
svIncrement x = svAddConstant x (1::Integer)

-- | Decrement:
svDecrement :: SVal -> SVal
svDecrement x = svAddConstant x (-1 :: Integer)

-- | Quotient: Overloaded operation whose meaning depends on the kind at which
-- it is used: For unbounded integers, it corresponds to the SMT-Lib
-- "div" operator ("Euclidean" division, which always has a
-- non-negative remainder). For unsigned bitvectors, it is "bvudiv";
-- and for signed bitvectors it is "bvsdiv", which rounds toward zero.
-- Division by 0 is defined s.t. @x/0 = 0@, which holds even when @x@ itself is @0@.
svQuot :: SVal -> SVal -> SVal
svQuot x y
  | isConcreteZero x = x
  | isConcreteZero y = svInteger (kindOf x) 0
  | isConcreteOne  y = x
  | True             = liftSym2 (mkSymOp Quot) [nonzeroCheck]
                                (noReal "quot") quot' (noFloat "quot") (noDouble "quot") (noFP "quot") (noRat "quot") x y
  where
    quot' a b | kindOf x == KUnbounded = div a (abs b) * signum b
              | otherwise              = quot a b

-- | Remainder: Overloaded operation whose meaning depends on the kind at which
-- it is used: For unbounded integers, it corresponds to the SMT-Lib
-- "mod" operator (always non-negative). For unsigned bitvectors, it
-- is "bvurem"; and for signed bitvectors it is "bvsrem", which rounds
-- toward zero (sign of remainder matches that of @x@). Division by 0 is
-- defined s.t. @x/0 = 0@, which holds even when @x@ itself is @0@.
svRem :: SVal -> SVal -> SVal
svRem x y
  | isConcreteZero x = x
  | isConcreteZero y = x
  | isConcreteOne  y = svInteger (kindOf x) 0
  | True             = liftSym2 (mkSymOp Rem) [nonzeroCheck]
                                (noReal "rem") rem' (noFloat "rem") (noDouble "rem") (noFP "rem") (noRat "rem") x y
  where
    rem' a b | kindOf x == KUnbounded = mod a (abs b)
             | otherwise              = rem a b

-- | Combination of quot and rem
svQuotRem :: SVal -> SVal -> (SVal, SVal)
svQuotRem x y = (x `svQuot` y, x `svRem` y)

-- | Implication. Only for booleans.
svImplies :: SVal -> SVal -> SVal
svImplies a b
  | any (\x -> kindOf x /= KBool) [a, b] = error $ "Data.SBV.svImplies: Unexpected arguments: " ++ show (a, kindOf a, b, kindOf b)
  | isConcreteZero a                     = svTrue  -- F -> _ = T
  |                     isConcreteOne  b = svTrue  -- _ -> T = T
  | isConcreteOne  a && isConcreteZero b = svFalse -- T -> F = F
  | isConcreteOne  a && isConcreteOne  b = svTrue  -- T -> T = T
  | True                                 = SVal KBool $ Right $ cache c
  where c st = do sva <- svToSV st a
                  svb <- svToSV st b
                  -- One final optimization, equal args is just True!
                  if sva == svb
                     then pure trueSV
                     else newExpr st KBool (SBVApp Implies [sva, svb])

-- | Strong equality. Only matters on floats, where it says @NaN@ equals @NaN@ and @+0@ and @-0@ are different.
-- Otherwise equivalent to `svEqual`.
svStrongEqual :: SVal -> SVal -> SVal
svStrongEqual x y | isFloat x,  Just f1 <- getF x,  Just f2 <- getF y  = svBool $ f1 `fpIsEqualObjectH` f2
                  | isDouble x, Just f1 <- getD x,  Just f2 <- getD y  = svBool $ f1 `fpIsEqualObjectH` f2
                  | isFP x,     Just f1 <- getFP x, Just f2 <- getFP y = svBool $ f1 `fpIsEqualObjectH` f2
                  | isFloat x || isDouble x || isFP x                  = SVal KBool $ Right $ cache r
                  | True                                               = compareSV (Equal True) x y
  where getF (SVal _ (Left (CV _ (CFloat f)))) = Just f
        getF _                                 = Nothing

        getD (SVal _ (Left (CV _ (CDouble d)))) = Just d
        getD _                                  = Nothing

        getFP (SVal _ (Left (CV _ (CFP f))))    = Just f
        getFP _                                 = Nothing

        r st = do sx <- svToSV st x
                  sy <- svToSV st y
                  newExpr st KBool (SBVApp (IEEEFP FP_ObjEqual) [sx, sy])

-- Comparisons have to be careful in making sure we don't rely on CVal ord/eq instance.
compareSV :: Op -> SVal -> SVal -> SVal
compareSV op x y
  -- Make sure we don't get anything we can't handle or expect
  | op `notElem` [Equal True, Equal False, NotEqual, LessThan, GreaterThan, LessEq, GreaterEq]
  = error $ "Unexpected call to compareSV: "              ++ show (op, x, y)
  | kx /= ky
  = error $ "Mismatched kinds in call to compareSV:"      ++ show (op, x, kindOf x, kindOf y)
  | (isSet kx || isArray ky) && op `notElem` [Equal True, Equal False, NotEqual]
  = error $ "Unexpected Set/Array not-equal comparison: " ++ show (op, x, k)

  -- Boolean equality optimizations
  | k == KBool, Equal{} <- op,    SVal _ (Left xv) <- x, xv == trueCV  = y       -- true  .== y     --> y
  | k == KBool, Equal{} <- op,    SVal _ (Left yv) <- y, yv == trueCV  = x       -- x     .== true  --> x
  | k == KBool, Equal{} <- op,    SVal _ (Left xv) <- x, xv == falseCV = svNot y -- false .== y     --> svNot y
  | k == KBool, Equal{} <- op,    SVal _ (Left yv) <- y, yv == falseCV = svNot x -- x     .== false --> svNot x

  | k == KBool, op == NotEqual, SVal _ (Left xv) <- x, xv == trueCV  = svNot y   -- true  ./= y     --> svNot y
  | k == KBool, op == NotEqual, SVal _ (Left yv) <- y, yv == trueCV  = svNot x   -- x     ./= true  --> svNot x
  | k == KBool, op == NotEqual, SVal _ (Left xv) <- x, xv == falseCV = y         -- false ./= y     --> y
  | k == KBool, op == NotEqual, SVal _ (Left yv) <- y, yv == falseCV = x         -- x     ./= false --> x

  -- Comparison optimizations if one operand is min/max bit-vector
  | op == LessThan,    isConcreteMax x = svFalse   -- MAX <  _
  | op == LessThan,    isConcreteMin y = svFalse   -- _   <  MIN

  | op == GreaterThan, isConcreteMin x = svFalse   -- MIN >  _
  | op == GreaterThan, isConcreteMax y = svFalse   -- _   > MAX

  | op == LessEq,      isConcreteMin x = svTrue    -- MIN <= _
  | op == LessEq,      isConcreteMax y = svTrue    -- _   <= MAX

  | op == GreaterEq,   isConcreteMax x = svTrue    -- MAX >= _
  | op == GreaterEq,   isConcreteMin y = svTrue    -- _   >= MIN

  -- General constant folding, but be careful not to be too smart here.
  | SVal _ (Left xv) <- x, SVal _ (Left yv) <- y
  = case cCompare k op (cvVal xv) (cvVal yv) of
      Nothing -> -- cCompare is conservative on floats. Give those one more chance, only at the top-level.
                 -- (i.e., if stored under a Maybe/Either/List etc., we'll resort to a symbolic result.)
                 case (k, cvVal xv, cvVal yv) of
                    (KFloat,   CFloat  a, CFloat  b) -> svBool (a `cFPOp` b)
                    (KDouble,  CDouble a, CDouble b) -> svBool (a `cFPOp` b)
                    (KFP{}  ,  CFP     a, CFP     b) -> svBool (a `cFPOp` b)
                    _                                -> symResult
      Just r  -> svBool $ case op of
                            Equal _     -> r == EQ
                            NotEqual    -> r /= EQ
                            LessThan    -> r == LT
                            GreaterThan -> r == GT
                            LessEq      -> r `elem` [EQ, LT]
                            GreaterEq   -> r `elem` [EQ, GT]
                            _           -> error $ "Unexpected call to compareSV: " ++ show (op, x, y)

   -- No constant folding opportunities, turn symbolic
   | True
   = symResult
   where kx = kindOf x
         ky = kindOf y
         k  = kx       -- only used after we ensured kx == ky

         -- Are there any floats embedded down from here? if so, we have to be careful due to presence of NaN
         safeEq =  op == Equal True       -- strong equality ok
                || isSomeKindOfFloat k    -- top level OK
                || not (containsFloats k) -- has floats somewhere: not ok

         symResult
           | safeEq = symResultSafe
           | True   = symResultFP

         -- This will go down to SMTLib's =. So only use it if we're safe to do so!
         symResultSafe = SVal KBool $ Right $ cache res
          where res st = do svx :: SV <- svToSV st x
                            svy :: SV <- svToSV st y

                            if svx == svy && eqCheckIsObjectEq k
                               then case op of
                                       Equal{}     -> pure trueSV
                                       LessEq      -> pure trueSV
                                       GreaterEq   -> pure trueSV
                                       NotEqual    -> pure falseSV
                                       LessThan    -> pure falseSV
                                       GreaterThan -> pure falseSV
                                       _           -> error $ "Unexpected call to compareSV, equal SV case: " ++ show (op, svx)
                               else newExpr st KBool (SBVApp op [svx, svy])

         a `cFPOp` b = case op of
                         Equal False -> a == b
                         Equal True  -> a `fpIsEqualObjectH` b
                         NotEqual    -> a /= b
                         LessThan    -> a <  b
                         GreaterThan -> a >  b
                         LessEq      -> a <= b
                         GreaterEq   -> a >= b
                         _           -> error $ "Unexpected call to cFPOp: " ++ show op

         -- OK, we have a result that has floats embedded in it. So comparison is problematic.
         -- Certain subsets of this is supported elsewhere. Here, we simply bail out.
         symResultFP = error $ unlines $  [ ""
                                          , "*** Data.SBV: Unsupported complicated comparison:"
                                          , "***"
                                          , "***   Op  : " ++ show op
                                          , "***   Type: " ++ show k
                                          , "***"
                                          , "*** Due to the presence of NaN, comparisons over this type require"
                                          , "*** special support in SMTLib. And in general this can lead to"
                                          , "*** performance issues since the comparison is no longer a natively"
                                          , "*** supported operation in the logic."
                                          , "***"
                                          , "*** NB. If you want the semantics NaN == NaN, and +0 /= -0, then you can use .=== instead."
                                          , "***"
                                          ]
                                       ++ case alternative of
                                            Nothing -> ["*** Please report this as a feature request."]
                                            Just a  -> [ "*** For this case, please use: " ++ a
                                                       , "*** but beware of performance/decidability implications."
                                                       ]

              where alternative = case (op, k) of
                                    (Equal False, KList f) | isFloat f || isDouble f || isFP f -> Just "Data.SBV.List.listEq"
                                    _                                                          -> Nothing

-- Compare two CVals; if we can. We're being conservative here and deferring to a symbolic result if we get something complicated.
cCompare :: Kind -> Op -> CVal -> CVal -> Maybe Ordering
cCompare k op x y =
    case (x, y) of

      -- The presence of NaN's throw this off. Why? Because @NaN `compare` x = GT@ in Haskell. But that's just the wrong thing to do here.
      -- So protect against NaN's. And a similar story for -0/0.
      (CFloat  a, CFloat  b) | any (nanOrZero k) [x, y] -> Nothing
                             | True                     -> Just $ a `compare` b

      (CDouble a, CDouble b) | any (nanOrZero k) [x, y] -> Nothing
                             | True                     -> Just $ a `compare` b

      (CFP     a, CFP     b) | any (nanOrZero k) [x, y] -> Nothing
                             | True                      -> Just $ a `compare` b

      -- Simple cases
      (CInteger  a, CInteger  b) -> Just $ a `compare` b
      (CRational a, CRational b) -> Just $ a `compare` b
      (CChar     a, CChar     b) -> Just $ a `compare` b
      (CString   a, CString   b) -> Just $ a `compare` b

      -- We can handle algreal, so long as they are exact-rationals
      (CAlgReal     a, CAlgReal  b) | isExactRational a && isExactRational b -> Just $ a `compare` b
                                    | True                                   -> Nothing

      -- Structural cases
      (CMaybe       a, CMaybe    b) -> case (a, b) of
                                         (Nothing, Nothing) -> Just EQ
                                         (Nothing, Just{})  -> Just LT
                                         (Just{},  Nothing) -> Just GT
                                         (Just av, Just bv) -> case k of
                                                                 KMaybe ke -> cCompare ke op av bv
                                                                 _         -> error $ "Unexpected kind in cCompare for maybe's: " ++ show k

      (CEither      a, CEither   b) -> let (kl, kr) = case k of
                                                        KEither l r -> (l, r)
                                                        _           -> error $ "Unexpected kind in cCompare for either's: " ++ show k
                                       in case (a, b) of
                                            (Left{},   Right{})  -> Just LT
                                            (Right{},  Left{})   -> Just GT
                                            (Left av,  Left  bv) -> cCompare kl op av bv
                                            (Right av, Right bv) -> cCompare kr op av bv

      -- Uninterpreted sorts use the index
      (CUserSort    a, CUserSort b) -> case (a, b) of
                                         ((Just i, _), (Just j, _)) -> Just $ i `compare` j
                                         _                          -> error $ "cCompare: Impossible happened while trying to compare: " ++ show (op, a, b)

      -- Lists and tuples use lexicographic ordering
      (CList        a, CList b) -> case k of
                                     KList ke -> lexCmp (map (ke,) a) (map (ke,) b)
                                     _        -> error $ "cCompare: Unexpected kind in cCompare for List: " ++ show k

      (CTuple       a, CTuple b) | length a == length b -> case k of
                                                             KTuple ks | length ks == length a -> lexCmp (zip ks a) (zip ks b)
                                                             _                                 -> error "cCompare: Unexpected kind in cCompare for tuples"
                                 | True                 -> error $ "cCompare: Received tuples of differing size: " ++ show (op, length a, length b, k)

      -- Arrays and sets only support equality/inequality. And they have object-equality semantics. So
      -- if there are any floats or non-exact-rationals down in the index or element kinds, we bail
      (CSet a, CSet b)     | op `elem` [Equal True, Equal False, NotEqual]
                           , KSet ke <- k
                           -> case svSetEqual ke a b of
                                 Nothing    -> Nothing  -- We don't know
                                 Just True  -> Just EQ  -- They're equal
                                 Just False -> Just $ if op `elem` [Equal True, Equal False]
                                                         then GT  -- Pick GT, So equality    test will fail
                                                         else EQ  -- Pick EQ, So in-equality test will fail
                           | True
                           -> error $ "cCompare: Received unexpected set comparison: " ++ show (op, k)

      (CArray a, CArray b) | op `elem` [Equal True, Equal False, NotEqual]
                           , KArray k1 k2 <- k
                           -> case svArrEqual k1 k2 a b of
                                Nothing    -> Nothing  -- We don't know
                                Just True  -> Just EQ  -- They're equal
                                Just False -> Just $ if op `elem` [Equal True, Equal False]
                                                        then GT  -- Pick GT, So equality    test will fail
                                                        else EQ  -- Pick EQ, So in-equality test will fail
                           | True
                           -> error $ "cCompare: Received unexpected array comparison: " ++ show (op, k)

      _ -> error $ unlines [ ""
                           , "*** Data.SBV.cCompare: Bug in SBV: Unhandled rank in comparison fallthru"
                           , "***"
                           , "***   Ranks Received: " ++ show (cvRank x, cvRank y)
                           , "***"
                           , "*** Please report this as a bug!"
                           ]
  where -- lexicographic
        lexCmp :: [(Kind, CVal)] -> [(Kind, CVal)] -> Maybe Ordering
        lexCmp []     []     = Just EQ
        lexCmp []     (_:_)  = Just LT
        lexCmp (_:_)  []     = Just GT
        lexCmp ((k1, a):as) ((k2, b):bs)
          | k1 == k2
          = case cCompare k1 op a b of
              Just EQ -> as `lexCmp` bs
              other   -> other
          | True
          = error $ "Mismatching kinds in lexicographic comparison: " ++ show (k1, k2)

        nanOrZero KFloat      (CFloat  v) = isNaN v || v == 0
        nanOrZero KDouble     (CDouble v) = isNaN v || v == 0
        nanOrZero (KFP eb sb) (CFP     v) = isNaN v || v == fpFromInteger eb sb 0
        nanOrZero knd         _           = error $ "Unexpected arguments to nanOrZero: " ++ show knd

        -- | Set equality. We return Nothing if the result is too complicated for us to concretely calculate.
        -- Why? Because the Eq instance of CVal is a bit iffy; it's designed to work as an index into maps, not as
        -- a means of checking this sort of equality
        svSetEqual :: Kind -> RCSet CVal -> RCSet CVal -> Maybe Bool
        svSetEqual ek sa sb
          | eqCheckIsObjectEq ek, RegularSet a    <- sa, RegularSet b    <- sb = Just $ a == b
          | eqCheckIsObjectEq ek, ComplementSet a <- sa, ComplementSet b <- sb = Just $ a == b
          | True                                                               = Nothing

        -- | Array equality. See above comments.
        svArrEqual :: Kind -> Kind -> ArrayModel CVal CVal -> ArrayModel CVal CVal -> Maybe Bool
        svArrEqual k1 k2 (ArrayModel asc1 def1) (ArrayModel asc2 def2)
         | not (all eqCheckIsObjectEq [k1, k2])
         = Nothing
         | True
         = let -- Use of lookup is safe here, because we already made sure equality is *not* problematic above
               keysMatch = and [key `lookup` asc1 == key `lookup` asc2 | key <- nub (sort (map fst (asc1 ++ asc2)))]
               defsMatch = def1 == def2

               -- Check if keys cover everything. Clearly, we can't do this for all kinds; but only finite ones
               -- For the time being, we're retricting ourselves to bool only. Might want to extend this later.
               complete  = case k1 of
                             KBool -> let bools       = map cvVal [falseCV, trueCV]
                                          covered asc = all (`elem` map fst asc) bools
                                      in covered asc1 && covered asc2
                             _     -> False

           in case (keysMatch, defsMatch, complete) of
                (False, _   ,  _)    -> Just False -- keys mismatch. Nothing else matters.
                (True,  True,  _)    -> Just True  -- keys match, def matches; so all is good. Complete doesn't matter.
                (True,  False, True) -> Just True  -- keys match, but defs don't. But we keys are complete, so def mismatch is OK
                _                    -> Nothing    -- otherwise, we don't really know. So, remain symbolic.

-- | Equality. This is SMT object equality.
svEqual :: SVal -> SVal -> SVal
svEqual = compareSV (Equal False)

-- | Inequality.
svNotEqual :: SVal -> SVal -> SVal
svNotEqual = compareSV NotEqual

-- | Less than.
svLessThan :: SVal -> SVal -> SVal
svLessThan = compareSV LessThan

-- | Greater than.
svGreaterThan :: SVal -> SVal -> SVal
svGreaterThan = compareSV GreaterThan

-- | Less than or equal to.
svLessEq :: SVal -> SVal -> SVal
svLessEq = compareSV LessEq

-- | Greater than or equal to.
svGreaterEq :: SVal -> SVal -> SVal
svGreaterEq = compareSV GreaterEq

-- | Bitwise and.
svAnd :: SVal -> SVal -> SVal
svAnd x y
  | isConcreteZero x = x
  | isConcreteOnes x = y
  | isConcreteZero y = y
  | isConcreteOnes y = x
  | True             = liftSym2 (mkSymOpSC opt And) [] (noReal ".&.") (.&.) (noFloat ".&.") (noDouble ".&.") (noFP ".&.") (noRat ".&") x y
  where opt a b
          | a == falseSV || b == falseSV = Just falseSV
          | a == trueSV                  = Just b
          | b == trueSV                  = Just a
          | a == b                       = Just a
          | True                         = Nothing

-- | Bitwise or.
svOr :: SVal -> SVal -> SVal
svOr x y
  | isConcreteZero x = y
  | isConcreteOnes x = x
  | isConcreteZero y = x
  | isConcreteOnes y = y
  | True             = liftSym2 (mkSymOpSC opt Or) []
                       (noReal ".|.") (.|.) (noFloat ".|.") (noDouble ".|.") (noFP ".|.") (noRat ".|.") x y
  where opt a b
          | a == trueSV || b == trueSV = Just trueSV
          | a == falseSV               = Just b
          | b == falseSV               = Just a
          | a == b                     = Just a
          | True                       = Nothing

-- | Bitwise xor.
svXOr :: SVal -> SVal -> SVal
svXOr x y
  | isConcreteZero x = y
  | isConcreteOnes x = svNot y
  | isConcreteZero y = x
  | isConcreteOnes y = svNot x
  | True             = liftSym2 (mkSymOpSC opt XOr) []
                       (noReal "xor") xor (noFloat "xor") (noDouble "xor") (noFP "xor") (noRat "xor") x y
  where opt a b
          | a == b && swKind a == KBool = Just falseSV
          | a == falseSV                = Just b
          | b == falseSV                = Just a
          | True                        = Nothing

-- | Bitwise complement.
svNot :: SVal -> SVal
svNot = liftSym1 (mkSymOp1SC opt Not)
                 (noRealUnary "complement") complement
                 (noFloatUnary "complement") (noDoubleUnary "complement") (noFPUnary "complement") (noRatUnary "complement")
  where opt a
          | a == falseSV = Just trueSV
          | a == trueSV  = Just falseSV
          | True         = Nothing

-- | Shift left by a constant amount. Translates to the "bvshl"
-- operation in SMT-Lib.
--
-- NB. Haskell spec says the behavior is undefined if the shift amount
-- is negative. We arbitrarily return the value unchanged if this is the case.
svShl :: SVal -> Int -> SVal
svShl x i
  | i <= 0
  = x
  | isBounded x, i >= intSizeOf x
  = svInteger k 0
  | True
  = x `svShiftLeft` svInteger k (fromIntegral i)
  where k = kindOf x

-- | Shift right by a constant amount. Translates to either "bvlshr"
-- (logical shift right) or "bvashr" (arithmetic shift right) in
-- SMT-Lib, depending on whether @x@ is a signed bitvector.
--
-- NB. Haskell spec says the behavior is undefined if the shift amount
-- is negative. We arbitrarily return the value unchanged if this is the case.
svShr :: SVal -> Int -> SVal
svShr x i
  | i <= 0
  = x
  | isBounded x, i >= intSizeOf x
  = if not (hasSign x)
       then z
       else svIte (x `svLessThan` z) neg1 z
  | True
  = x `svShiftRight` svInteger k (fromIntegral i)
  where k    = kindOf x
        z    = svInteger k 0
        neg1 = svInteger k (-1)

-- | Rotate-left, by a constant.
--
-- NB. Haskell spec says the behavior is undefined if the shift amount
-- is negative. We arbitrarily return the value unchanged if this is the case.
svRol :: SVal -> Int -> SVal
svRol x i
  | i <= 0
  = x
  | True
  = case kindOf x of
           KBounded _ sz -> liftSym1 (mkSymOp1 (Rol (i `mod` sz)))
                                     (noRealUnary "rotateL") (rot True sz i)
                                     (noFloatUnary "rotateL") (noDoubleUnary "rotateL") (noFPUnary "rotateL") (noRatUnary "rotateL") x
           _ -> svShl x i   -- for unbounded Integers, rotateL is the same as shiftL in Haskell

-- | Rotate-right, by a constant.
--
-- NB. Haskell spec says the behavior is undefined if the shift amount
-- is negative. We arbitrarily return the value unchanged if this is the case.
svRor :: SVal -> Int -> SVal
svRor x i
  | i <= 0
  = x
  | True
  = case kindOf x of
      KBounded _ sz -> liftSym1 (mkSymOp1 (Ror (i `mod` sz)))
                                (noRealUnary "rotateR") (rot False sz i)
                                (noFloatUnary "rotateR") (noDoubleUnary "rotateR") (noFPUnary "rotateR") (noRatUnary "rotateR") x
      _ -> svShr x i   -- for unbounded integers, rotateR is the same as shiftR in Haskell

-- | Generic rotation. Since the underlying representation is just Integers, rotations has to be
-- careful on the bit-size.
rot :: Bool -> Int -> Int -> Integer -> Integer
rot toLeft sz amt x
  | sz < 2 = x
  | True   = norm x y' `shiftL` y  .|. norm (x `shiftR` y') y
  where (y, y') | toLeft = (amt `mod` sz, sz - y)
                | True   = (sz - y', amt `mod` sz)
        norm v s = v .&. ((1 `shiftL` s) - 1)

-- | Extract bit-sequences.
svExtract :: Int -> Int -> SVal -> SVal
svExtract i j x@(SVal (KBounded s _) _)
  | i < j
  = SVal k (Left $! CV k (CInteger 0))
  | SVal _ (Left (CV _ (CInteger v))) <- x
  = SVal k (Left $! normCV (CV k (CInteger (v `shiftR` j))))
  | True
  = SVal k (Right (cache y))
  where k = KBounded s (i - j + 1)
        y st = do sv <- svToSV st x
                  newExpr st k (SBVApp (Extract i j) [sv])
svExtract i j v@(SVal KFloat _)  = svExtract i j (svFloatAsSWord32  v)
svExtract i j v@(SVal KDouble _) = svExtract i j (svDoubleAsSWord64 v)
svExtract i j v@(SVal KFP{} _)   = svExtract i j (svFloatingPointAsSWord v)
svExtract _ _ _ = error "extract: non-bitvector/float type"

-- | Join two words, by concatenating
svJoin :: SVal -> SVal -> SVal
svJoin x@(SVal (KBounded s i) a) y@(SVal (KBounded s' j) b)
  | s /= s'
  = error $ "svJoin: received differently signed values: " ++ show (x, y)
  | i == 0 = y
  | j == 0 = x
  | Left (CV _ (CInteger m)) <- a, Left (CV _ (CInteger n)) <- b
  = let val
         | s -- signed, arithmetic doesn't work; blast and come back
         = let xbits = [m `testBit` xi | xi <- [0 .. i-1]]
               ybits = [n `testBit` yi | yi <- [0 .. j-1]]
               rbits = zip [0..] (ybits ++ xbits)
           in foldl' (\acc (idx, set) -> if set then setBit acc idx else acc) 0 rbits
         | True -- unsigned, go fast
         = m `shiftL` j .|. n
    in SVal k (Left $! normCV (CV k (CInteger val)))
  | True
  = SVal k (Right (cache z))
  where
    k = KBounded s (i + j)
    z st = do xsw <- svToSV st x
              ysw <- svToSV st y
              newExpr st k (SBVApp Join [xsw, ysw])
svJoin _ _ = error "svJoin: non-bitvector type"

-- | Zero-extend by given number of bits.
svZeroExtend :: Int -> SVal -> SVal
svZeroExtend = svExtend True ZeroExtend

-- | Sign-extend by given number of bits.
svSignExtend :: Int -> SVal -> SVal
svSignExtend = svExtend False SignExtend

svExtend :: Bool -> (Int -> Op) -> Int -> SVal -> SVal
svExtend isZeroExtend extender i x@(SVal (KBounded s sz) a)
  | i < 0
  = error $ "svExtend: Received negative extension amount: " ++ show i
  | i == 0
  = x
  | Left (CV _ (CInteger cv)) <- a
  = SVal k' (Left (normCV (CV k' (CInteger (replBit (not isZeroExtend && (cv `testBit` (sz-1))) cv)))))
  | True
  = SVal k' (Right (cache z))
  where k' = KBounded s (sz+i)
        z st = do xsw <- svToSV st x
                  newExpr st k' (SBVApp (extender i) [xsw])

        replBit :: Bool -> Integer -> Integer
        replBit b = go sz
          where stop = sz + i
                go k v | k == stop = v
                       | b         = go (k+1) (v `setBit`   k)
                       | True      = go (k+1) (v `clearBit` k)

svExtend _ _ _ _ = error "svExtend: non-bitvector type"

-- | If-then-else. This one will force branches.
svIte :: SVal -> SVal -> SVal -> SVal
svIte t a b = svSymbolicMerge (kindOf a) True t a b

-- | Lazy If-then-else. This one will delay forcing the branches unless it's really necessary.
svLazyIte :: Kind -> SVal -> SVal -> SVal -> SVal
svLazyIte k t a b = svSymbolicMerge k False t a b

-- | Merge two symbolic values, at kind @k@, possibly @force@'ing the branches to make
-- sure they do not evaluate to the same result.
svSymbolicMerge :: Kind -> Bool -> SVal -> SVal -> SVal -> SVal
svSymbolicMerge k force t a b
  | Just r <- svAsBool t
  = if r then a else b
  | force, rationalSBVCheck a b, sameResult a b
  = a
  | True
  = SVal k $ Right $ cache c
  where sameResult (SVal _ (Left c1)) (SVal _ (Left c2)) = c1 == c2
        sameResult _                  _                  = False

        c st = do swt <- svToSV st t
                  case () of
                    () | swt == trueSV  -> svToSV st a       -- these two cases should never be needed as we expect symbolicMerge to be
                    () | swt == falseSV -> svToSV st b       -- called with symbolic tests, but just in case..
                    () -> do {- It is tempting to record the choice of the test expression here as we branch down to the 'then' and 'else' branches. That is,
                                when we evaluate @a@, we can make use of the fact that the test expression is True, and similarly we can use the fact that it
                                is False when @b@ is evaluated. In certain cases this can cut down on symbolic simulation significantly, for instance if
                                repetitive decisions are made in a recursive loop. Unfortunately, the implementation of this idea is quite tricky, due to
                                our sharing based implementation. As the 'then' branch is evaluated, we will create many expressions that are likely going
                                to be "reused" when the 'else' branch is executed. But, it would be *dead wrong* to share those values, as they were "cached"
                                under the incorrect assumptions. To wit, consider the following:

                                   foo x y = ite (y .== 0) k (k+1)
                                     where k = ite (y .== 0) x (x+1)

                                When we reduce the 'then' branch of the first ite, we'd record the assumption that y is 0. But while reducing the 'then' branch, we'd
                                like to share @k@, which would evaluate (correctly) to @x@ under the given assumption. When we backtrack and evaluate the 'else'
                                branch of the first ite, we'd see @k@ is needed again, and we'd look it up from our sharing map to find (incorrectly) that its value
                                is @x@, which was stored there under the assumption that y was 0, which no longer holds. Clearly, this is unsound.

                                A sound implementation would have to precisely track which assumptions were active at the time expressions get shared. That is,
                                in the above example, we should record that the value of @k@ was cached under the assumption that @y@ is 0. While sound, this
                                approach unfortunately leads to significant loss of valid sharing when the value itself had nothing to do with the assumption itself.
                                To wit, consider:

                                   foo x y = ite (y .== 0) k (k+1)
                                     where k = x+5

                                If we tracked the assumptions, we would recompute @k@ twice, since the branch assumptions would differ. Clearly, there is no need to
                                re-compute @k@ in this case since its value is independent of @y@. Note that the whole SBV performance story is based on aggressive sharing,
                                and losing that would have other significant ramifications.

                                The "proper" solution would be to track, with each shared computation, precisely which assumptions it actually *depends* on, rather
                                than blindly recording all the assumptions present at that time. SBV's symbolic simulation engine clearly has all the info needed to do this
                                properly, but the implementation is not straightforward at all. For each subexpression, we would need to chase down its dependencies
                                transitively, which can require a lot of scanning of the generated program causing major slow-down; thus potentially defeating the
                                whole purpose of sharing in the first place.

                                Design choice: Keep it simple, and simply do not track the assumption at all. This will maximize sharing, at the cost of evaluating
                                unreachable branches. I think the simplicity is more important at this point than efficiency.

                                Also note that the user can avoid most such issues by properly combining if-then-else's with common conditions together. That is, the
                                first program above should be written like this:

                                  foo x y = ite (y .== 0) x (x+2)

                                In general, the following transformations should be done whenever possible:

                                  ite e1 (ite e1 e2 e3) e4  --> ite e1 e2 e4
                                  ite e1 e2 (ite e1 e3 e4)  --> ite e1 e2 e4

                                This is in accordance with the general rule-of-thumb stating conditionals should be avoided as much as possible. However, we might prefer
                                the following:

                                  ite e1 (f e2 e4) (f e3 e5) --> f (ite e1 e2 e3) (ite e1 e4 e5)

                                especially if this expression happens to be inside 'f's body itself (i.e., when f is recursive), since it reduces the number of
                                recursive calls. Clearly, programming with symbolic simulation in mind is another kind of beast altogether.
                             -}
                             let sta = st `extendSValPathCondition` svAnd t
                             let stb = st `extendSValPathCondition` svAnd (svNot t)
                             swa <- svToSV sta a -- evaluate 'then' branch
                             swb <- svToSV stb b -- evaluate 'else' branch

                             -- merge, but simplify for certain boolean cases:
                             case () of
                               () | swa == swb                      -> return swa                                     -- if t then a      else a     ==> a
                               () | swa == trueSV && swb == falseSV -> return swt                                     -- if t then true   else false ==> t
                               () | swa == falseSV && swb == trueSV -> newExpr st k (SBVApp Not [swt])                -- if t then false  else true  ==> not t
                               () | swa == trueSV                   -> newExpr st k (SBVApp Or  [swt, swb])           -- if t then true   else b     ==> t OR b
                               () | swa == falseSV                  -> do swt' <- newExpr st KBool (SBVApp Not [swt])
                                                                          newExpr st k (SBVApp And [swt', swb])       -- if t then false  else b     ==> t' AND b
                               () | swb == trueSV                   -> do swt' <- newExpr st KBool (SBVApp Not [swt])
                                                                          newExpr st k (SBVApp Or [swt', swa])        -- if t then a      else true  ==> t' OR a
                               () | swb == falseSV                  -> newExpr st k (SBVApp And [swt, swa])           -- if t then a      else false ==> t AND a
                               ()                                   -> newExpr st k (SBVApp Ite [swt, swa, swb])

-- | Total indexing operation. @svSelect xs default index@ is
-- intuitively the same as @xs !! index@, except it evaluates to
-- @default@ if @index@ overflows. Translates to SMT-Lib tables.
svSelect :: [SVal] -> SVal -> SVal -> SVal
svSelect xs err ind
  | SVal _ (Left c) <- ind =
    case cvVal c of
      CInteger i -> if i < 0 || i >= genericLength xs
                    then err
                    else xs `genericIndex` i
      _          -> error $ "SBV.select: unsupported " ++ show (kindOf ind) ++ " valued select/index expression"
svSelect xsOrig err ind = xs `seq` SVal kElt (Right (cache r))
  where
    kInd = kindOf ind
    kElt = kindOf err
    -- Based on the index size, we need to limit the elements. For
    -- instance if the index is 8 bits, but there are 257 elements,
    -- that last element will never be used and we can chop it off.
    xs = case kInd of
           KBounded False i -> genericTake ((2::Integer) ^ i) xsOrig
           KBounded True  i -> genericTake ((2::Integer) ^ (i-1)) xsOrig
           KUnbounded       -> xsOrig
           _                -> error $ "SBV.select: unsupported " ++ show kInd ++ " valued select/index expression"
    r st = do sws <- mapM (svToSV st) xs
              swe <- svToSV st err
              if all (== swe) sws  -- off-chance that all elts are the same
                 then return swe
                 else do idx <- getTableIndex st kInd kElt sws
                         swi <- svToSV st ind
                         let len = length xs
                         -- NB. No need to worry here that the index
                         -- might be < 0; as the SMTLib translation
                         -- takes care of that automatically
                         newExpr st kElt (SBVApp (LkUp (idx, kInd, kElt, len) swi swe) [])

-- Change the sign of a bit-vector quantity. Fails if passed a non-bv
svChangeSign :: Bool -> SVal -> SVal
svChangeSign s x
  | not (isBounded x)       = error $ "Data.SBV." ++ nm ++ ": Received non bit-vector kind: " ++ show (kindOf x)
  | Just n <- svAsInteger x = svInteger k n
  | True                    = SVal k (Right (cache y))
  where
    nm = if s then "svSign" else "svUnsign"

    k = KBounded s (intSizeOf x)
    y st = do xsw <- svToSV st x
              newExpr st k (SBVApp (Extract (intSizeOf x - 1) 0) [xsw])

-- | Convert a symbolic bitvector from unsigned to signed.
svSign :: SVal -> SVal
svSign = svChangeSign True

-- | Convert a symbolic bitvector from signed to unsigned.
svUnsign :: SVal -> SVal
svUnsign = svChangeSign False

-- | Convert a symbolic bitvector from one integral kind to another.
svFromIntegral :: Kind -> SVal -> SVal
svFromIntegral kTo x
  | Just v <- svAsInteger x
  = svInteger kTo v
  | True
  = result
  where result = SVal kTo (Right (cache y))
        kFrom  = kindOf x
        y st   = do xsw <- svToSV st x
                    newExpr st kTo (SBVApp (KindCast kFrom kTo) [xsw])

--------------------------------------------------------------------------------
-- Derived operations

-- | Convert an SVal from kind Bool to an unsigned bitvector of size 1.
svToWord1 :: SVal -> SVal
svToWord1 b = svSymbolicMerge k True b (svInteger k 1) (svInteger k 0)
  where k = KBounded False 1

-- | Convert an SVal from a bitvector of size 1 (signed or unsigned) to kind Bool.
svFromWord1 :: SVal -> SVal
svFromWord1 x = svNotEqual x (svInteger k 0)
  where k = kindOf x

-- | Test the value of a bit. Note that we do an extract here
-- as opposed to masking and checking against zero, as we found
-- extraction to be much faster with large bit-vectors.
svTestBit :: SVal -> Int -> SVal
svTestBit x i
  | i < intSizeOf x = svFromWord1 (svExtract i i x)
  | True            = svFalse

-- | Generalization of 'svShl', where the shift-amount is symbolic.
svShiftLeft :: SVal -> SVal -> SVal
svShiftLeft = svShift True

-- | Generalization of 'svShr', where the shift-amount is symbolic.
--
-- NB. If the shiftee is signed, then this is an arithmetic shift;
-- otherwise it's logical.
svShiftRight :: SVal -> SVal -> SVal
svShiftRight = svShift False

-- | Generic shifting of bounded quantities. The shift amount must be non-negative and within the bounds of the argument
-- for bit vectors. For negative shift amounts, the result is returned unchanged. For overshifts, left-shift produces 0,
-- right shift produces 0 or -1 depending on the result being signed.
svShift :: Bool -> SVal -> SVal -> SVal
svShift toLeft x i
  | Just r <- constFoldValue
  = r
  | cannotOverShift
  = svIte (i `svLessThan` svInteger ki 0)                                         -- Negative shift, no change
          x
          regularShiftValue
  | True
  = svIte (i `svLessThan` svInteger ki 0)                                         -- Negative shift, no change
          x
          $ svIte (i `svGreaterEq` svInteger ki (fromIntegral (intSizeOf x)))     -- Overshift, by at least the bit-width of x
                  overShiftValue
                  regularShiftValue

  where nm | toLeft = "shiftLeft"
           | True   = "shiftRight"

        kx = kindOf x
        ki = kindOf i

        -- Constant fold the result if possible. If either quantity is unbounded, then we only support constants
        -- as there's no easy/meaningful way to map this combo to SMTLib. Should be rarely needed, if ever!
        -- We also perform basic sanity check here so that if we go past here, we know we have bitvectors only.
        constFoldValue
          | Just iv <- getConst i, iv == 0
          = Just x

          | Just xv <- getConst x, xv == 0
          = Just x

          | Just xv <- getConst x, Just iv <- getConst i
          = Just $ SVal kx . Left $! normCV $ CV kx (CInteger (xv `opC` shiftAmount iv))

          | isUnbounded x || isUnbounded i
          = bailOut $ "Not yet implemented unbounded/non-constants shifts for " ++ show (kx, ki) ++ ", please file a request!"

          | not (isBounded x && isBounded i)
          = bailOut $ "Unexpected kinds: " ++ show (kx, ki)

          | True
          = Nothing

          where bailOut m = error $ "SBV." ++ nm ++ ": " ++ m

                getConst (SVal _ (Left (CV _ (CInteger val)))) = Just val
                getConst _                                     = Nothing

                opC | toLeft = shiftL
                    | True   = shiftR

                -- like fromIntegral, but more paranoid
                shiftAmount :: Integer -> Int
                shiftAmount iv
                  | iv <= 0                                            = 0
                  | isUnbounded i, iv > fromIntegral (maxBound :: Int) = bailOut $ "Unsupported constant unbounded shift with amount: " ++ show iv
                  | isUnbounded x                                      = fromIntegral iv
                  | iv >= fromIntegral ub                              = ub
                  | not (isBounded x && isBounded i)                   = bailOut $ "Unsupported kinds: " ++ show (kx, ki)
                  | True                                               = fromIntegral iv
                 where ub = intSizeOf x

        -- Overshift is not possible if the bit-size of x won't even fit into the bit-vector size
        -- of i. Note that this is a *necessary* check, Consider for instance if we're shifting a
        -- 32-bit value using a 1-bit shift amount (which can happen if the value is 1 with minimal
        -- shift widths). We would compare 1 >= 32, but stuffing 32 into bit-vector of size 1 would
        -- overflow. See http://github.com/LeventErkok/sbv/issues/323 for this case. Thus, we
        -- make sure that the bit-vector would fit as a value.
        cannotOverShift = maxRepresentable <= fromIntegral (intSizeOf x)
          where maxRepresentable :: Integer
                maxRepresentable
                  | hasSign i = bit (intSizeOf i - 1) - 1
                  | True      = bit (intSizeOf i    ) - 1

        -- An overshift occurs if we're shifting by more than or equal to the bit-width of x
        --     For shift-left: this value is always 0
        --     For shift-right:
        --        If x is unsigned: 0
        --        If x is signed and is less than 0, then -1 else 0
        overShiftValue | toLeft    = zx
                       | hasSign x = svIte (x `svLessThan` zx) neg1 zx
                       | True      = zx
          where zx   = svInteger kx 0
                neg1 = svInteger kx (-1)

        -- Regular shift, we know that the shift value fits into the bit-width of x, since it's between 0 and sizeOf x. So, we can just
        -- turn it into a properly sized argument and ship it to SMTLib
        regularShiftValue = SVal kx $ Right $ cache result
           where result st = do sw1 <- svToSV st x
                                sw2 <- svToSV st i

                                let op | toLeft = Shl
                                       | True   = Shr

                                adjustedShift <- if kx == ki
                                                 then return sw2
                                                 else newExpr st kx (SBVApp (KindCast ki kx) [sw2])

                                newExpr st kx (SBVApp op [sw1, adjustedShift])

-- | A variant of 'svRotateLeft' that uses a barrel-rotate design, which can lead to
-- better verification code. Only works when both arguments are finite and the second
-- argument is unsigned.
svBarrelRotateLeft :: SVal -> SVal -> SVal
svBarrelRotateLeft x i
  | not (isBounded x && isBounded i && not (hasSign i))
  = error $ "Data.SBV.Dynamic.svBarrelRotateLeft: Arguments must be bounded with second argument unsigned. Received: " ++ show (x, i)
  | Just iv <- svAsInteger i
  = svRol x $ fromIntegral (iv `rem` fromIntegral (intSizeOf x))
  | True
  = barrelRotate svRol x i

-- | A variant of 'svRotateLeft' that uses a barrel-rotate design, which can lead to
-- better verification code. Only works when both arguments are finite and the second
-- argument is unsigned.
svBarrelRotateRight :: SVal -> SVal -> SVal
svBarrelRotateRight x i
  | not (isBounded x && isBounded i && not (hasSign i))
  = error $ "Data.SBV.Dynamic.svBarrelRotateRight: Arguments must be bounded with second argument unsigned. Received: " ++ show (x, i)
  | Just iv <- svAsInteger i
  = svRor x $ fromIntegral (iv `rem` fromIntegral (intSizeOf x))
  | True
  = barrelRotate svRor x i

-- Barrel rotation, by bit-blasting the argument:
barrelRotate :: (SVal -> Int -> SVal) -> SVal -> SVal -> SVal
barrelRotate f a c = loop blasted a
  where loop :: [(SVal, Integer)] -> SVal -> SVal
        loop []              acc = acc
        loop ((b, v) : rest) acc = loop rest (svIte b (f acc (fromInteger v)) acc)

        sa = toInteger $ intSizeOf a
        n  = svInteger (kindOf c) sa

        -- Reduce by the modulus amount, we need not care about the
        -- any part larger than the value of the bit-size of the
        -- argument as it is identity for rotations
        reducedC = c `svRem` n

        -- blast little-endian, and zip with bit-position
        blasted = takeWhile significant $ zip (svBlastLE reducedC) [2^i | i <- [(0::Integer)..]]

        -- Any term whose bit-position is larger than our input size
        -- is insignificant, since the reduction would've put 0's in those
        -- bits. For instance, if a is 32 bits, and c is 5 bits, then we
        -- need not look at any position i s.t. 2^i > 32
        significant (_, pos) = pos < sa

-- | Generalization of 'svRol', where the rotation amount is symbolic.
-- If the first argument is not bounded, then the this is the same as shift.
svRotateLeft :: SVal -> SVal -> SVal
svRotateLeft = svRotate svShiftLeft svRor svRol

-- | Generalization of 'svRor', where the rotation amount is symbolic.
-- If the first argument is not bounded, then the this is the same as shift.
svRotateRight :: SVal -> SVal -> SVal
svRotateRight = svRotate svShiftRight svRol svRor

-- | Common implementation for rotations. This is more complicated than it might first seem, since SMTLib does
-- not allow for non-constant rotation amounts, and only defines rotations for bit-vectors. In SBV, we support
-- both finite/infinite combos, and also non-constant (i.e., symbolic) rotations. Furthermore, if the rotation
-- amount is negative, then the direction of the rotation is reversed.
--
--   Case 1. Infinite x. In this case, we call unbounded-shifter, since you can't rotate an unbounded integer value.
--                       This is the Haskell semantics for rotates.
--   Case 2. Finite x.
--           Case 2.1. Infinite i, or finite i but i can contain a value > |x|. In this case, wrap-around can happen,
--                     so we reduce by the size of |x|.
--           Case 2.2. Finite i, and it can't contain a value > |x|. In this case, no reduction is needed.
svRotate :: (SVal -> SVal -> SVal) -> (SVal -> Int -> SVal) -> (SVal -> Int -> SVal) -> SVal -> SVal -> SVal
svRotate unboundedShifter opRot curRot x i
  | not (isBounded x)
  = unboundedShifter x i
  | True
  = svSelect table (svInteger (kindOf x) 0) curRotate
 where sx = intSizeOf x
       si = intSizeOf i

       -- Is it the case that this rotation can never "wrap-around?" This happens if
       -- i is bounded and the max rotation it can represent is less than the bit-size of the input
       noWrapAround :: Bool
       noWrapAround = isBounded i && maxRotate <= toInteger sx
         where maxRotate :: Integer
               maxRotate
                 | hasSign i = 2^(si-1)
                 | True      = 2^si-1

       ifNegRotate = svIte (svLessThan i (svInteger (kindOf i) 0))

       -- the lookup table has sx entries if index can wrap-around. Otherwise it is just as wide as it needs to be.
       table :: [SVal]
       table = map rotK vals
         where rotK k = ifNegRotate (x `opRot` k) (x `curRot` k)
               vals | noWrapAround = if hasSign i
                                        then -- If signed then bit (si-1) is the max abs value. (consider 3 bits, [-4..3] is the range)
                                             [0 .. bit (si - 1)]
                                        else [0 .. bit si  - 1]
                    | True  -- If wrap-around can happen, then compute all rotations up to |x|
                    = [0 .. sx - 1]

       -- What's the current rotation amount? Here we change the type of the
       -- index to make it one bit larger if the index is signed, since otherwise
       -- we run into (-(-1)) = -1 problem. See https://github.com/LeventErkok/sbv/issues/673#issuecomment-1782296700
       -- Note that curRotate is always non-negative.
       curRotate :: SVal
       curRotate
         | noWrapAround = ifNegRotate (svUNeg i'          ) i'
         | True         = ifNegRotate (svUNeg i' `svRem` n) (i' `svRem` n)

         where i' | hasSign i && isBounded i = toWord $ svAbs $ enlarge i
                  | True                     = i

               -- Make sure sx can fit into this many bits
               si' = (si + 1) `max` bitsNeeded sx

               enlarge
                 | isBounded i = svFromIntegral (KBounded True  si')  -- Increase bit size
                 | True        = id
               toWord
                 | isBounded i = svFromIntegral (KBounded False si')  -- Treat as word, after call to svAbs above
                 | True        = id

               n = svInteger (kindOf i') (toInteger sx)

               bitsNeeded :: Int -> Int
               bitsNeeded = go 0
                 where go s 0 = s
                       go s v = let s' = s + 1 in s' `seq` go s' (v `shiftR` 1)

--------------------------------------------------------------------------------
-- | Overflow detection.
svMkOverflow1 :: OvOp -> SVal -> SVal
svMkOverflow1 o x = SVal KBool (Right (cache r))
    where r st = do sx <- svToSV st x
                    newExpr st KBool $ SBVApp (OverflowOp o) [sx]

svMkOverflow2 :: OvOp -> SVal -> SVal -> SVal
svMkOverflow2 o x y = SVal KBool (Right (cache r))
    where r st = do sx <- svToSV st x
                    sy <- svToSV st y
                    newExpr st KBool $ SBVApp (OverflowOp o) [sx, sy]

--------------------------------------------------------------------------------
-- Utility functions

liftSym1 :: (State -> Kind -> SV -> IO SV) -> (AlgReal  -> AlgReal)
                                           -> (Integer  -> Integer)
                                           -> (Float    -> Float)
                                           -> (Double   -> Double)
                                           -> (FP       -> FP)
                                           -> (Rational -> Rational)
                                           -> SVal      -> SVal
liftSym1 _   opCR opCI opCF opCD opFP opRA   (SVal k (Left a)) = SVal k . Left  $! mapCV opCR opCI opCF opCD opFP opRA a
liftSym1 opS _    _    _    _    _    _    a@(SVal k _)        = SVal k $ Right $ cache c
   where c st = do sva <- svToSV st a
                   opS st k sva

{- A note on constant folding.

There are cases where we miss out on certain constant foldings. On May 8 2018, Matt Peddie pointed this
out, as the C code he was getting had redundancies. I was aware that could be missing constant foldings
due to missed out optimizations, or some other code snafu, but till Matt pointed it out I haven't realized
that we could be hiding constants inside an if-then-else. The example is:

     proveWith z3{verbose=True} $ \x -> 0 .< ite (x .== (x::SWord8)) 1 (2::SWord8)

If you try this, you'll see that it generates (shortened):

    (define-fun s1 () (_ BitVec 8) #x00)
    (define-fun s2 () (_ BitVec 8) #x01)
    (define-fun s3 () Bool (bvult s1 s2))

But clearly we have all the info for s3 to be computed! The issue here is that the reduction of @x .== x@ to @true@
happens after we start computing the if-then-else, hence we are already committed to an SV at that point. The call
to ite eventually recognizes this, but at that point it picks up the now constants from SV's, missing the constant
folding opportunity.

We can fix this, by looking up the constants table in liftSV2, along the lines of:


    liftSV2 :: (CV -> CV -> Bool) -> (CV -> CV -> CV) -> (State -> Kind -> SV -> SV -> IO SV) -> Kind -> SVal -> SVal -> Cached SV
    liftSV2 okCV opCV opS k a b = cache c
      where c st = do sw1 <- svToSV st a
                      sw2 <- svToSV st b
                      cmap <- readIORef (rconstMap st)
                      let cv1  = [cv | ((_, cv), sv) <- M.toList cmap, sv == sv1]
                          cv2  = [cv | ((_, cv), sv) <- M.toList cmap, sv == sv2]
                      case (cv1, cv2) of
                        ([x], [y]) | okCV x y -> newConst st $ opCV x y
                        _                     -> opS st k sv1 sv2

(with obvious modifications to call sites to get the proper arguments.)

But this means that we have to grab the constant list for every symbolically lifted operation, also do the
same for other places, etc.; for the rare opportunity of catching a @x .== x@ optimization. Even then, the
constants for the branches would still be generated. (i.e., in the above example we would still generate
@s1@ and @s2@, but would skip @s3@.)

It seems to me that the price to pay is rather high, as this is hardly the most common case; so we're opting
here to ignore these cases.

See http://github.com/LeventErkok/sbv/issues/379 for some further discussion.
-}
liftSV2 :: (State -> Kind -> SV -> SV -> IO SV) -> Kind -> SVal -> SVal -> Cached SV
liftSV2 opS k a b = cache c
  where c st = do sw1 <- svToSV st a
                  sw2 <- svToSV st b
                  opS st k sw1 sw2

liftSym2 :: (State -> Kind -> SV -> SV -> IO SV)
         -> [CV       -> CV      -> Bool]
         -> (AlgReal  -> AlgReal -> AlgReal)
         -> (Integer  -> Integer -> Integer)
         -> (Float    -> Float   -> Float)
         -> (Double   -> Double  -> Double)
         -> (FP       -> FP      -> FP)
         -> (Rational -> Rational-> Rational)
         -> SVal      -> SVal    -> SVal
liftSym2 _   okCV opCR opCI opCF opCD opFP opRA (SVal k (Left a)) (SVal _ (Left b)) | and [f a b | f <- okCV] = SVal k . Left  $! mapCV2 opCR opCI opCF opCD opFP opRA a b
liftSym2 opS _    _    _    _    _    _  _      a@(SVal k _)      b                                           = SVal k $ Right $  liftSV2 opS k a b

-- | Create a symbolic two argument operation; with shortcut optimizations
mkSymOpSC :: (SV -> SV -> Maybe SV) -> Op -> State -> Kind -> SV -> SV -> IO SV
mkSymOpSC shortCut op st k a b = maybe (newExpr st k (SBVApp op [a, b])) return (shortCut a b)

-- | Create a symbolic two argument operation; no shortcut optimizations
mkSymOp :: Op -> State -> Kind -> SV -> SV -> IO SV
mkSymOp = mkSymOpSC (const (const Nothing))

mkSymOp1SC :: (SV -> Maybe SV) -> Op -> State -> Kind -> SV -> IO SV
mkSymOp1SC shortCut op st k a = maybe (newExpr st k (SBVApp op [a])) return (shortCut a)

mkSymOp1 :: Op -> State -> Kind -> SV -> IO SV
mkSymOp1 = mkSymOp1SC (const Nothing)

-- | Predicate to check if a value is concrete
isConcrete :: SVal -> Bool
isConcrete (SVal _ Left{}) = True
isConcrete _               = False

-- | Predicate for optimizing word operations like (+) and (*).
-- NB. We specifically do *not* match for Double/Float; because
-- FP-arithmetic doesn't obey traditional rules. For instance,
-- 0 * x = 0 fails if x happens to be NaN or +/- Infinity. So,
-- we merely return False when given a floating-point value here.
isConcreteZero :: SVal -> Bool
isConcreteZero (SVal _     (Left (CV _     (CInteger n)))) = n == 0
isConcreteZero (SVal KReal (Left (CV KReal (CAlgReal v)))) = isExactRational v && v == 0
isConcreteZero _                                           = False

-- | Predicate for optimizing word operations like (+) and (*).
-- NB. See comment on 'isConcreteZero' for why we don't match
-- for Float/Double values here.
isConcreteOne :: SVal -> Bool
isConcreteOne (SVal _     (Left (CV _     (CInteger 1)))) = True
isConcreteOne (SVal KReal (Left (CV KReal (CAlgReal v)))) = isExactRational v && v == 1
isConcreteOne _                                           = False

-- | Predicate for optimizing bitwise operations. The unbounded integer case of checking
-- against -1 might look dubious, but that's how Haskell treats 'Integer' as a member
-- of the Bits class, try @(-1 :: Integer) `testBit` i@ for any @i@ and you'll get 'True'.
isConcreteOnes :: SVal -> Bool
isConcreteOnes (SVal _ (Left (CV (KBounded b w) (CInteger n)))) = n == if b then -1 else bit w - 1
isConcreteOnes (SVal _ (Left (CV KUnbounded     (CInteger n)))) = n == -1  -- see comment above
isConcreteOnes (SVal _ (Left (CV KBool          (CInteger n)))) = n == 1
isConcreteOnes _                                                = False

-- | Predicate for optimizing comparisons.
isConcreteMax :: SVal -> Bool
isConcreteMax (SVal _ (Left (CV (KBounded False w) (CInteger n)))) = n == bit w - 1
isConcreteMax (SVal _ (Left (CV (KBounded True  w) (CInteger n)))) = n == bit (w - 1) - 1
isConcreteMax (SVal _ (Left (CV KBool              (CInteger n)))) = n == 1
isConcreteMax _                                                    = False

-- | Predicate for optimizing comparisons.
isConcreteMin :: SVal -> Bool
isConcreteMin (SVal _ (Left (CV (KBounded False _) (CInteger n)))) = n == 0
isConcreteMin (SVal _ (Left (CV (KBounded True  w) (CInteger n)))) = n == - bit (w - 1)
isConcreteMin (SVal _ (Left (CV KBool              (CInteger n)))) = n == 0
isConcreteMin _                                                    = False

-- | Most operations on concrete rationals require a compatibility check to avoid faulting
-- on algebraic reals.
rationalCheck :: CV -> CV -> Bool
rationalCheck a b = case (cvVal a, cvVal b) of
                     (CAlgReal x, CAlgReal y) -> isExactRational x && isExactRational y
                     _                        -> True

-- | Quot/Rem operations require a nonzero check on the divisor.
nonzeroCheck :: CV -> CV -> Bool
nonzeroCheck _ b = cvVal b /= CInteger 0

-- | Same as rationalCheck, except for SBV's
rationalSBVCheck :: SVal -> SVal -> Bool
rationalSBVCheck (SVal KReal (Left a)) (SVal KReal (Left b)) = rationalCheck a b
rationalSBVCheck _                     _                     = True

noReal :: String -> AlgReal -> AlgReal -> a
noReal o a b = error $ "SBV.AlgReal." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noFloat :: String -> Float -> Float -> a
noFloat o a b = error $ "SBV.Float." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noDouble :: String -> Double -> Double -> a
noDouble o a b = error $ "SBV.Double." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noFP :: String -> FP -> FP -> a
noFP o a b = error $ "SBV.FPR." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noRat:: String -> Rational -> Rational -> a
noRat o a b = error $ "SBV.Rational." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noRealUnary :: String -> AlgReal -> a
noRealUnary o a = error $ "SBV.AlgReal." ++ o ++ ": Unexpected argument: " ++ show a

noFloatUnary :: String -> Float -> a
noFloatUnary o a = error $ "SBV.Float." ++ o ++ ": Unexpected argument: " ++ show a

noDoubleUnary :: String -> Double -> a
noDoubleUnary o a = error $ "SBV.Double." ++ o ++ ": Unexpected argument: " ++ show a

noFPUnary :: String -> FP -> a
noFPUnary o a = error $ "SBV.FPR." ++ o ++ ": Unexpected argument: " ++ show a

noRatUnary :: String -> Rational -> a
noRatUnary o a = error $ "SBV.Rational." ++ o ++ ": Unexpected argument: " ++ show a

-- | Given a composite structure, figure out how to compare for less than
svStructuralLessThan :: SVal -> SVal -> SVal
svStructuralLessThan x y
   | isConcrete x && isConcrete y
   = x `svLessThan` y
   | KTuple{} <- kx
   = tupleLT x y
   | KMaybe{}  <- kx
   = maybeLT x y
   | KEither{} <- kx
   = eitherLT x y
   | True
   = x `svLessThan` y
   where kx = kindOf x

-- | Structural less-than for tuples
tupleLT :: SVal -> SVal -> SVal
tupleLT x y = SVal KBool $ Right $ cache res
  where ks = case kindOf x of
               KTuple xs -> xs
               k         -> error $ "Data.SBV: Impossible happened, tupleLT called with: " ++ show (k, x, y)

        n = length ks

        res st = do sx <- svToSV st x
                    sy <- svToSV st y

                    let chkElt i ek = let xi = SVal ek $ Right $ cache $ \_ -> newExpr st ek $ SBVApp (TupleAccess i n) [sx]
                                          yi = SVal ek $ Right $ cache $ \_ -> newExpr st ek $ SBVApp (TupleAccess i n) [sy]
                                          lt = xi `svStructuralLessThan` yi
                                          eq = xi `svEqual`              yi
                                       in (lt, eq)

                        walk []                  = svFalse
                        walk [(lti, _)]          = lti
                        walk ((lti, eqi) : rest) = lti `svOr` (eqi `svAnd` walk rest)

                    svToSV st $ walk $ zipWith chkElt [1..] ks

-- | Structural less-than for maybes
maybeLT :: SVal -> SVal -> SVal
maybeLT x y = sMaybeCase (       sMaybeCase svFalse (const svTrue)    y)
                         (\jx -> sMaybeCase svFalse (jx `svStructuralLessThan`) y)
                         x
  where ka = case kindOf x of
               KMaybe k' -> k'
               k         -> error $ "Data.SBV: Impossible happened, maybeLT called with: " ++ show (k, x, y)

        sMaybeCase brNothing brJust s = SVal KBool $ Right $ cache res
           where res st = do sv <- svToSV st s

                             let justVal = SVal ka $ Right $ cache $ \_ -> newExpr st ka $ SBVApp MaybeAccess [sv]
                                 justRes = brJust justVal

                             br1 <- svToSV st brNothing
                             br2 <- svToSV st justRes

                             -- Do we have a value?
                             noVal <- newExpr st KBool $ SBVApp (MaybeIs ka False) [sv]
                             newExpr st KBool $ SBVApp Ite [noVal, br1, br2]

-- | Structural less-than for either
eitherLT :: SVal -> SVal -> SVal
eitherLT x y = sEitherCase (\lx -> sEitherCase (lx `svStructuralLessThan`) (const svTrue)              y)
                           (\rx -> sEitherCase (const svFalse)             (rx `svStructuralLessThan`) y)
                           x
  where (ka, kb) = case kindOf x of
                     KEither k1 k2 -> (k1, k2)
                     k             -> error $ "Data.SBV: Impossible happened, eitherLT called with: " ++ show (k, x, y)

        sEitherCase brA brB sab = SVal KBool $ Right $ cache res
          where res st = do abv <- svToSV st sab

                            let leftVal  = SVal ka $ Right $ cache $ \_ -> newExpr st ka $ SBVApp (EitherAccess False) [abv]
                                rightVal = SVal kb $ Right $ cache $ \_ -> newExpr st kb $ SBVApp (EitherAccess True)  [abv]

                                leftRes  = brA leftVal
                                rightRes = brB rightVal

                            br1 <- svToSV st leftRes
                            br2 <- svToSV st rightRes

                            --  Which branch are we in? Return the appropriate value:
                            onLeft <- newExpr st KBool $ SBVApp (EitherIs ka kb False) [abv]
                            newExpr st KBool $ SBVApp Ite [onLeft, br1, br2]

-- | Convert an 'Data.SBV.SFloat' to an 'Data.SBV.SWord32', preserving the bit-correspondence. Note that since the
-- representation for @NaN@s are not unique, this function will return a symbolic value when given a
-- concrete @NaN@.
--
-- Implementation note: Since there's no corresponding function in SMTLib for conversion to
-- bit-representation due to partiality, we use a translation trick by allocating a new word variable,
-- converting it to float, and requiring it to be equivalent to the input. In code-generation mode, we simply map
-- it to a simple conversion.
svFloatAsSWord32 :: SVal -> SVal
svFloatAsSWord32 (SVal KFloat (Left (CV KFloat (CFloat f))))
   | not (isNaN f)
   = let w32 = KBounded False 32
     in SVal w32 $ Left $ CV w32 $ CInteger (fromIntegral (floatToWord f))
svFloatAsSWord32 fVal@(SVal KFloat _)
  = SVal w32 (Right (cache y))
  where w32  = KBounded False 32
        y st = do cg <- isCodeGenMode st
                  if cg
                     then do f <- svToSV st fVal
                             newExpr st w32 (SBVApp (IEEEFP (FP_Reinterpret KFloat w32)) [f])
                     else do n   <- newInternalVariable st w32
                             ysw <- newExpr st KFloat (SBVApp (IEEEFP (FP_Reinterpret w32 KFloat)) [n])
                             internalConstraint st False [] $ fVal `svStrongEqual` SVal KFloat (Right (cache (\_ -> return ysw)))
                             return n
svFloatAsSWord32 (SVal k _) = error $ "svFloatAsSWord32: non-float type: " ++ show k

-- | Convert an 'Data.SBV.SDouble' to an 'Data.SBV.SWord64', preserving the bit-correspondence. Note that since the
-- representation for @NaN@s are not unique, this function will return a symbolic value when given a
-- concrete @NaN@.
--
-- Implementation note: Since there's no corresponding function in SMTLib for conversion to
-- bit-representation due to partiality, we use a translation trick by allocating a new word variable,
-- converting it to float, and requiring it to be equivalent to the input. In code-generation mode, we simply map
-- it to a simple conversion.
svDoubleAsSWord64 :: SVal -> SVal
svDoubleAsSWord64 (SVal KDouble (Left (CV KDouble (CDouble f))))
   | not (isNaN f)
   = let w64 = KBounded False 64
     in SVal w64 $ Left $ CV w64 $ CInteger (fromIntegral (doubleToWord f))
svDoubleAsSWord64 fVal@(SVal KDouble _)
  = SVal w64 (Right (cache y))
  where w64  = KBounded False 64
        y st = do cg <- isCodeGenMode st
                  if cg
                     then do f <- svToSV st fVal
                             newExpr st w64 (SBVApp (IEEEFP (FP_Reinterpret KDouble w64)) [f])
                     else do n   <- newInternalVariable st w64
                             ysw <- newExpr st KDouble (SBVApp (IEEEFP (FP_Reinterpret w64 KDouble)) [n])
                             internalConstraint st False [] $ fVal `svStrongEqual` SVal KDouble (Right (cache (\_ -> return ysw)))
                             return n
svDoubleAsSWord64 (SVal k _) = error $ "svDoubleAsSWord64: non-float type: " ++ show k

-- | Convert a float to the word containing the corresponding bit pattern
svFloatingPointAsSWord :: SVal -> SVal
svFloatingPointAsSWord (SVal (KFP eb sb) (Left (CV _ (CFP f@(FP _ _ fpV)))))
  | not (isNaN f)
  = let wN = KBounded False (eb + sb)
    in SVal wN $ Left $ CV wN $ CInteger $ bfToBits (mkBFOpts eb sb NearEven) fpV
svFloatingPointAsSWord fVal@(SVal kFrom@(KFP eb sb) _)
  = SVal kTo (Right (cache y))
  where kTo   = KBounded False (eb + sb)
        y st = do cg <- isCodeGenMode st
                  if cg
                     then do f <- svToSV st fVal
                             newExpr st kTo (SBVApp (IEEEFP (FP_Reinterpret kFrom kTo)) [f])
                     else do n   <- newInternalVariable st kTo
                             ysw <- newExpr st kFrom (SBVApp (IEEEFP (FP_Reinterpret kTo kFrom)) [n])
                             internalConstraint st False [] $ fVal `svStrongEqual` SVal kFrom (Right (cache (\_ -> return ysw)))
                             return n
svFloatingPointAsSWord (SVal k _) = error $ "svFloatingPointAsSWord: non-float type: " ++ show k

{- HLint ignore svIte     "Eta reduce"         -}
{- HLint ignore svLazyIte "Eta reduce"         -}
{- HLint ignore module    "Reduce duplication" -}
