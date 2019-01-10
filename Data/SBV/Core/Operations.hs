-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Operations
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Constructors and basic operations on symbolic values
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}

module Data.SBV.Core.Operations
  (
  -- ** Basic constructors
    svTrue, svFalse, svBool
  , svInteger, svFloat, svDouble, svReal, svEnumFromThenTo, svString, svChar
  -- ** Basic destructors
  , svAsBool, svAsInteger, svNumerator, svDenominator
  -- ** Basic operations
  , svPlus, svTimes, svMinus, svUNeg, svAbs
  , svDivide, svQuot, svRem, svQuotRem
  , svEqual, svNotEqual
  , svLessThan, svGreaterThan, svLessEq, svGreaterEq
  , svAnd, svOr, svXOr, svNot
  , svShl, svShr, svRol, svRor
  , svExtract, svJoin
  , svIte, svLazyIte, svSymbolicMerge
  , svSelect
  , svSign, svUnsign, svSetBit, svWordFromBE, svWordFromLE
  , svExp, svFromIntegral
  -- ** Overflows
  , svMkOverflow
  -- ** Derived operations
  , svToWord1, svFromWord1, svTestBit
  , svShiftLeft, svShiftRight
  , svRotateLeft, svRotateRight
  , svBlastLE, svBlastBE
  , svAddConstant, svIncrement, svDecrement
  -- ** Basic array operations
  , SArr,         readSArr,     writeSArr,     mergeSArr,     newSArr,     eqSArr
  , SFunArr(..),  readSFunArr,  writeSFunArr,  mergeSFunArr,  newSFunArr
  -- Utils
  , mkSymOp
  )
  where

import Data.Bits (Bits(..))
import Data.List (genericIndex, genericLength, genericTake)

import qualified Data.IORef         as R    (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict    as Map  (toList, fromList, lookup)
import qualified Data.IntMap.Strict as IMap (IntMap, empty, toAscList, fromAscList, lookup, size, insert)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic

import Data.Ratio

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

-- | Convert from a Float
svDouble :: Double -> SVal
svDouble d = SVal KDouble (Left $! CV KDouble (CDouble d))

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
  | True             = liftSym2 (mkSymOp Plus) rationalCheck (+) (+) (+) (+) x y

-- | Multiplication.
svTimes :: SVal -> SVal -> SVal
svTimes x y
  | isConcreteZero x = x
  | isConcreteZero y = y
  | isConcreteOne x  = y
  | isConcreteOne y  = x
  | True             = liftSym2 (mkSymOp Times) rationalCheck (*) (*) (*) (*) x y

-- | Subtraction.
svMinus :: SVal -> SVal -> SVal
svMinus x y
  | isConcreteZero y = x
  | True             = liftSym2 (mkSymOp Minus) rationalCheck (-) (-) (-) (-) x y

-- | Unary minus.
svUNeg :: SVal -> SVal
svUNeg = liftSym1 (mkSymOp1 UNeg) negate negate negate negate

-- | Absolute value.
svAbs :: SVal -> SVal
svAbs = liftSym1 (mkSymOp1 Abs) abs abs abs abs

-- | Division.
svDivide :: SVal -> SVal -> SVal
svDivide = liftSym2 (mkSymOp Quot) rationalCheck (/) idiv (/) (/)
   where idiv x 0 = x
         idiv x y = x `div` y

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

-- | Bit-blast: Little-endian. Assumes the input is a bit-vector.
svBlastLE :: SVal -> [SVal]
svBlastLE x = map (svTestBit x) [0 .. intSizeOf x - 1]

-- | Set a given bit at index
svSetBit :: SVal -> Int -> SVal
svSetBit x i = x `svOr` svInteger (kindOf x) (bit i :: Integer)

-- | Bit-blast: Big-endian. Assumes the input is a bit-vector.
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
  | True             = liftSym2 (mkSymOp Quot) nonzeroCheck
                                (noReal "quot") quot' (noFloat "quot") (noDouble "quot") x y
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
  | True             = liftSym2 (mkSymOp Rem) nonzeroCheck
                                (noReal "rem") rem' (noFloat "rem") (noDouble "rem") x y
  where
    rem' a b | kindOf x == KUnbounded = mod a (abs b)
             | otherwise              = rem a b

-- | Combination of quot and rem
svQuotRem :: SVal -> SVal -> (SVal, SVal)
svQuotRem x y = (x `svQuot` y, x `svRem` y)

-- | Optimize away x == true and x /= false to x; otherwise just do eqOpt
eqOptBool :: Op -> SV -> SV -> SV -> Maybe SV
eqOptBool op w x y
  | k == KBool && op == Equal    && x == trueSV  = Just y         -- true  .== y     --> y
  | k == KBool && op == Equal    && y == trueSV  = Just x         -- x     .== true  --> x
  | k == KBool && op == NotEqual && x == falseSV = Just y         -- false ./= y     --> y
  | k == KBool && op == NotEqual && y == falseSV = Just x         -- x     ./= false --> x
  | True                                         = eqOpt w x y    -- fallback
  where k = swKind x

-- | Equality.
svEqual :: SVal -> SVal -> SVal
svEqual = liftSym2B (mkSymOpSC (eqOptBool Equal trueSV) Equal) rationalCheck (==) (==) (==) (==) (==) (==) (==) (==) (==)

-- | Inequality.
svNotEqual :: SVal -> SVal -> SVal
svNotEqual = liftSym2B (mkSymOpSC (eqOptBool NotEqual falseSV) NotEqual) rationalCheck (/=) (/=) (/=) (/=) (/=) (/=) (/=) (/=) (/=)

-- | Less than.
svLessThan :: SVal -> SVal -> SVal
svLessThan x y
  | isConcreteMax x = svFalse
  | isConcreteMin y = svFalse
  | True            = liftSym2B (mkSymOpSC (eqOpt falseSV) LessThan) rationalCheck (<) (<) (<) (<) (<) (<) (<) (<) (uiLift "<" (<)) x y

-- | Greater than.
svGreaterThan :: SVal -> SVal -> SVal
svGreaterThan x y
  | isConcreteMin x = svFalse
  | isConcreteMax y = svFalse
  | True            = liftSym2B (mkSymOpSC (eqOpt falseSV) GreaterThan) rationalCheck (>) (>) (>) (>) (>) (>) (>) (>) (uiLift ">"  (>)) x y

-- | Less than or equal to.
svLessEq :: SVal -> SVal -> SVal
svLessEq x y
  | isConcreteMin x = svTrue
  | isConcreteMax y = svTrue
  | True            = liftSym2B (mkSymOpSC (eqOpt trueSV) LessEq) rationalCheck (<=) (<=) (<=) (<=) (<=) (<=) (<=) (<=) (uiLift "<=" (<=)) x y

-- | Greater than or equal to.
svGreaterEq :: SVal -> SVal -> SVal
svGreaterEq x y
  | isConcreteMax x = svTrue
  | isConcreteMin y = svTrue
  | True            = liftSym2B (mkSymOpSC (eqOpt trueSV) GreaterEq) rationalCheck (>=) (>=) (>=) (>=) (>=) (>=) (>=) (>=) (uiLift ">=" (>=)) x y

-- | Bitwise and.
svAnd :: SVal -> SVal -> SVal
svAnd x y
  | isConcreteZero x = x
  | isConcreteOnes x = y
  | isConcreteZero y = y
  | isConcreteOnes y = x
  | True             = liftSym2 (mkSymOpSC opt And) (const (const True)) (noReal ".&.") (.&.) (noFloat ".&.") (noDouble ".&.") x y
  where opt a b
          | a == falseSV || b == falseSV = Just falseSV
          | a == trueSV                  = Just b
          | b == trueSV                  = Just a
          | True                         = Nothing

-- | Bitwise or.
svOr :: SVal -> SVal -> SVal
svOr x y
  | isConcreteZero x = y
  | isConcreteOnes x = x
  | isConcreteZero y = x
  | isConcreteOnes y = y
  | True             = liftSym2 (mkSymOpSC opt Or) (const (const True))
                       (noReal ".|.") (.|.) (noFloat ".|.") (noDouble ".|.") x y
  where opt a b
          | a == trueSV || b == trueSV = Just trueSV
          | a == falseSV               = Just b
          | b == falseSV               = Just a
          | True                       = Nothing

-- | Bitwise xor.
svXOr :: SVal -> SVal -> SVal
svXOr x y
  | isConcreteZero x = y
  | isConcreteOnes x = svNot y
  | isConcreteZero y = x
  | isConcreteOnes y = svNot x
  | True             = liftSym2 (mkSymOpSC opt XOr) (const (const True))
                       (noReal "xor") xor (noFloat "xor") (noDouble "xor") x y
  where opt a b
          | a == b && swKind a == KBool = Just falseSV
          | a == falseSV                = Just b
          | b == falseSV                = Just a
          | True                        = Nothing

-- | Bitwise complement.
svNot :: SVal -> SVal
svNot = liftSym1 (mkSymOp1SC opt Not)
                 (noRealUnary "complement") complement
                 (noFloatUnary "complement") (noDoubleUnary "complement")
  where opt a
          | a == falseSV = Just trueSV
          | a == trueSV  = Just falseSV
          | True         = Nothing

-- | Shift left by a constant amount. Translates to the "bvshl"
-- operation in SMT-Lib.
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

-- | Rotate-left, by a constant
svRol :: SVal -> Int -> SVal
svRol x i
  | i <= 0
  = x
  | True
  = case kindOf x of
           KBounded _ sz -> liftSym1 (mkSymOp1 (Rol (i `mod` sz)))
                                     (noRealUnary "rotateL") (rot True sz i)
                                     (noFloatUnary "rotateL") (noDoubleUnary "rotateL") x
           _ -> svShl x i   -- for unbounded Integers, rotateL is the same as shiftL in Haskell

-- | Rotate-right, by a constant
svRor :: SVal -> Int -> SVal
svRor x i
  | i <= 0
  = x
  | True
  = case kindOf x of
      KBounded _ sz -> liftSym1 (mkSymOp1 (Ror (i `mod` sz)))
                                (noRealUnary "rotateR") (rot False sz i)
                                (noFloatUnary "rotateR") (noDoubleUnary "rotateR") x
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
svExtract _ _ _ = error "extract: non-bitvector type"

-- | Join two words, by concataneting
svJoin :: SVal -> SVal -> SVal
svJoin x@(SVal (KBounded s i) a) y@(SVal (KBounded _ j) b)
  | i == 0 = y
  | j == 0 = x
  | Left (CV _ (CInteger m)) <- a, Left (CV _ (CInteger n)) <- b
  = SVal k (Left $! CV k (CInteger (m `shiftL` j .|. n)))
  | True
  = SVal k (Right (cache z))
  where
    k = KBounded s (i + j)
    z st = do xsw <- svToSV st x
              ysw <- svToSV st y
              newExpr st k (SBVApp Join [xsw, ysw])
svJoin _ _ = error "svJoin: non-bitvector type"

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
                                when we evaluate 'a', we can make use of the fact that the test expression is True, and similarly we can use the fact that it
                                is False when b is evaluated. In certain cases this can cut down on symbolic simulation significantly, for instance if
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
                                re-compute @k@ in this case since its value is independent of @y@. Note that the whole SBV performance story is based on agressive sharing,
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
                                recursive calls. Clearly, programming with symbolic simulation in mind is another kind of beast alltogether.
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

svChangeSign :: Bool -> SVal -> SVal
svChangeSign s x
  | Just n <- svAsInteger x = svInteger k n
  | True                    = SVal k (Right (cache y))
  where
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

          | isInteger x || isInteger i
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
                  | iv <= 0                                          = 0
                  | isInteger i, iv > fromIntegral (maxBound :: Int) = bailOut $ "Unsupported constant unbounded shift with amount: " ++ show iv
                  | isInteger x                                      = fromIntegral iv
                  | iv >= fromIntegral ub                            = ub
                  | not (isBounded x && isBounded i)                 = bailOut $ "Unsupported kinds: " ++ show (kx, ki)
                  | True                                             = fromIntegral iv
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

-- | Generalization of 'svRol', where the rotation amount is symbolic.
-- If the first argument is not bounded, then the this is the same as shift.
svRotateLeft :: SVal -> SVal -> SVal
svRotateLeft x i
  | not (isBounded x)
  = svShiftLeft x i
  | isBounded i && bit si <= toInteger sx            -- wrap-around not possible
  = svIte (svLessThan i zi)
          (svSelect [x `svRor` k | k <- [0 .. bit si - 1]] z (svUNeg i))
          (svSelect [x `svRol` k | k <- [0 .. bit si - 1]] z         i)
  | True
  = svIte (svLessThan i zi)
          (svSelect [x `svRor` k | k <- [0 .. sx     - 1]] z (svUNeg i `svRem` n))
          (svSelect [x `svRol` k | k <- [0 .. sx     - 1]] z (       i `svRem` n))
    where sx = intSizeOf x
          si = intSizeOf i
          z  = svInteger (kindOf x) 0
          zi = svInteger (kindOf i) 0
          n  = svInteger (kindOf i) (toInteger sx)

-- | Generalization of 'svRor', where the rotation amount is symbolic.
-- If the first argument is not bounded, then the this is the same as shift.
svRotateRight :: SVal -> SVal -> SVal
svRotateRight x i
  | not (isBounded x)
  = svShiftRight x i
  | isBounded i && bit si <= toInteger sx                   -- wrap-around not possible
  = svIte (svLessThan i zi)
          (svSelect [x `svRol` k | k <- [0 .. bit si - 1]] z (svUNeg i))
          (svSelect [x `svRor` k | k <- [0 .. bit si - 1]] z         i)
  | True
  = svIte (svLessThan i zi)
          (svSelect [x `svRol` k | k <- [0 .. sx     - 1]] z (svUNeg i `svRem` n))
          (svSelect [x `svRor` k | k <- [0 .. sx     - 1]] z (       i `svRem` n))
    where sx = intSizeOf x
          si = intSizeOf i
          z  = svInteger (kindOf x) 0
          zi = svInteger (kindOf i) 0
          n  = svInteger (kindOf i) (toInteger sx)

--------------------------------------------------------------------------------
-- | Overflow detection.
svMkOverflow :: OvOp -> SVal -> SVal -> SVal
svMkOverflow o x y = SVal KBool (Right (cache r))
    where r st = do sx <- svToSV st x
                    sy <- svToSV st y
                    newExpr st KBool $ SBVApp (OverflowOp o) [sx, sy]

---------------------------------------------------------------------------------
-- * Symbolic Arrays
---------------------------------------------------------------------------------

-- | Arrays in terms of SMT-Lib arrays
data SArr = SArr (Kind, Kind) (Cached ArrayIndex)

-- | Read the array element at @a@
readSArr :: SArr -> SVal -> SVal
readSArr (SArr (_, bk) f) a = SVal bk $ Right $ cache r
  where r st = do arr <- uncacheAI f st
                  i   <- svToSV st a
                  newExpr st bk (SBVApp (ArrRead arr) [i])

-- | Update the element at @a@ to be @b@
writeSArr :: SArr -> SVal -> SVal -> SArr
writeSArr (SArr ainfo f) a b = SArr ainfo $ cache g
  where g st = do arr  <- uncacheAI f st
                  addr <- svToSV st a
                  val  <- svToSV st b
                  amap <- R.readIORef (rArrayMap st)

                  let j   = ArrayIndex $ IMap.size amap
                      upd = IMap.insert (unArrayIndex j) ("array_" ++ show j, ainfo, ArrayMutate arr addr val)

                  j `seq` modifyState st rArrayMap upd $ modifyIncState st rNewArrs upd
                  return j

-- | Merge two given arrays on the symbolic condition
-- Intuitively: @mergeArrays cond a b = if cond then a else b@.
-- Merging pushes the if-then-else choice down on to elements
mergeSArr :: SVal -> SArr -> SArr -> SArr
mergeSArr t (SArr ainfo a) (SArr _ b) = SArr ainfo $ cache h
  where h st = do ai <- uncacheAI a st
                  bi <- uncacheAI b st
                  ts <- svToSV st t
                  amap <- R.readIORef (rArrayMap st)

                  let k   = ArrayIndex $ IMap.size amap
                      upd = IMap.insert (unArrayIndex k) ("array_" ++ show k, ainfo, ArrayMerge ts ai bi)

                  k `seq` modifyState st rArrayMap upd $ modifyIncState st rNewArrs upd
                  return k

-- | Create a named new array
newSArr :: State -> (Kind, Kind) -> (Int -> String) -> Maybe SVal -> IO SArr
newSArr st ainfo mkNm mbDef = do
    amap <- R.readIORef $ rArrayMap st

    mbSWDef <- case mbDef of
                 Nothing -> return Nothing
                 Just sv -> Just <$> svToSV st sv

    let i   = ArrayIndex $ IMap.size amap
        nm  = mkNm (unArrayIndex i)
        upd = IMap.insert (unArrayIndex i) (nm, ainfo, ArrayFree mbSWDef)

    registerLabel "SArray declaration" st nm

    modifyState st rArrayMap upd $ modifyIncState st rNewArrs upd
    return $ SArr ainfo $ cache $ const $ return i

-- | Compare two arrays for equality
eqSArr :: SArr -> SArr -> SVal
eqSArr (SArr _ a) (SArr _ b) = SVal KBool $ Right $ cache c
  where c st = do ai <- uncacheAI a st
                  bi <- uncacheAI b st
                  newExpr st KBool (SBVApp (ArrEq ai bi) [])

-- | Arrays managed internally
data SFunArr = SFunArr (Kind, Kind) (Cached FArrayIndex)

-- | Convert a node-id to an SVal
nodeIdToSVal :: Kind -> Int -> SVal
nodeIdToSVal k i = swToSVal $ SV k (NodeId i)

-- | Convert an 'SV' to an 'SVal'
swToSVal :: SV -> SVal
swToSVal sv@(SV k _) = SVal k $ Right $ cache $ const $ return sv

-- | A variant of SVal equality, but taking into account of constants
-- NB. The rationalCheck is paranid perhaps, but is necessary in case
-- we have some funky polynomial roots in there. We do allow for
-- floating-points here though. Why? Because the Eq instance of 'CV'
-- does the right thing by using object equality. (i.e., it does
-- the right thing for NaN/+0/-0 etc.) A straightforward equality
-- here would be wrong for floats!
svEqualWithConsts :: (SVal, Maybe CV) -> (SVal, Maybe CV) -> SVal
svEqualWithConsts sv1 sv2 = case (grabCV sv1, grabCV sv2) of
                               (Just cv, Just cv') | rationalCheck cv cv' -> if cv == cv' then svTrue else svFalse
                               _                                          -> fst sv1 `svEqual` fst sv2
  where grabCV (_,                Just cv) = Just cv
        grabCV (SVal _ (Left cv), _      ) = Just cv
        grabCV _                           = Nothing

-- | Read the array element at @a@. For efficiency purposes, we create a memo-table
-- as we go along, as otherwise we suffer significant performance penalties. See:
-- <http://github.com/LeventErkok/sbv/issues/402> and
-- <http://github.com/LeventErkok/sbv/issues/396>.
readSFunArr :: SFunArr -> SVal -> SVal
readSFunArr (SFunArr (ak, bk) f) address
  | kindOf address /= ak
  = error $ "Data.SBV.readSFunArr: Impossible happened, accesing with address type: " ++ show (kindOf address) ++ ", expected: " ++ show ak
  | True
  = SVal bk $ Right $ cache r
  where r st = do fArrayIndex <- uncacheFAI f st
                  fArrMap     <- R.readIORef (rFArrayMap st)

                  constMap <- R.readIORef (rconstMap st)
                  let consts = Map.fromList [(i, cv) | (cv, SV _ (NodeId i)) <- Map.toList constMap]

                  case unFArrayIndex fArrayIndex `IMap.lookup` fArrMap of
                    Nothing -> error $ "Data.SBV.readSFunArr: Impossible happened while trying to access SFunArray, can't find index: " ++ show fArrayIndex
                    Just (uninitializedRead, rCache) -> do
                        memoTable  <- R.readIORef rCache
                        SV _ (NodeId addressNodeId) <- svToSV st address

                        -- If we hit the cache, return the result right away. If we miss, we need to
                        -- walk through each element to "merge" all possible reads as we do not know
                        -- whether the symbolic access may end up the same as one of the earlier ones
                        -- in the cache.
                        case addressNodeId `IMap.lookup` memoTable of
                          Just v  -> return v  -- cache hit!

                          Nothing -> -- cache miss; walk down the cache items to form the chain of reads:
                                     do let aInfo = (address, addressNodeId `Map.lookup` consts)

                                            find :: [(Int, SV)] -> SVal
                                            find []             = uninitializedRead address
                                            find ((i, v) : ivs) = svIte (svEqualWithConsts (nodeIdToSVal ak i, i `Map.lookup` consts) aInfo) (swToSVal v) (find ivs)

                                            finalValue = find (IMap.toAscList memoTable)

                                        finalSW <- svToSV st finalValue

                                        -- Cache the result, so next time we can retrieve it faster if we look it up with the same address!
                                        -- The following line is really the whole point of having caching in SFunArray!
                                        R.modifyIORef' rCache (IMap.insert addressNodeId finalSW)

                                        return finalSW

-- | Update the element at @address@ to be @b@
writeSFunArr :: SFunArr -> SVal -> SVal -> SFunArr
writeSFunArr (SFunArr (ak, bk) f) address b
  | kindOf address /= ak
  = error $ "Data.SBV.writeSFunArr: Impossible happened, accesing with address type: " ++ show (kindOf address) ++ ", expected: " ++ show ak
  | kindOf b /= bk
  = error $ "Data.SBV.writeSFunArr: Impossible happened, accesing with address type: " ++ show (kindOf b) ++ ", expected: " ++ show bk
  | True
  = SFunArr (ak, bk) $ cache g
  where g st = do fArrayIndex <- uncacheFAI f st
                  fArrMap     <- R.readIORef (rFArrayMap st)
                  constMap    <- R.readIORef (rconstMap st)

                  let consts = Map.fromList [(i, cv) | (cv, SV _ (NodeId i)) <- Map.toList constMap]

                  case unFArrayIndex fArrayIndex `IMap.lookup` fArrMap of
                    Nothing          -> error $ "Data.SBV.writeSFunArr: Impossible happened while trying to access SFunArray, can't find index: " ++ show fArrayIndex

                    Just (aUi, rCache) -> do
                       memoTable <- R.readIORef rCache
                       SV _ (NodeId addressNodeId) <- svToSV st address
                       val                         <- svToSV st b

                       -- There are three cases:
                       --
                       --    (1) We hit the cache, and old value is the same as new: No write necessary, just return the array
                       --    (2) We hit the cache, values are different. Simply insert, overriding the old-memo table location
                       --    (3) We miss the cache: Now we have to walk through all accesses and update the memo table accordingly.
                       --        Why? Just because we missed the cache doesn't mean that it's not there with a different "symbolic"
                       --        address. So, we have to walk through and update each entry in case the address matches.
                       --
                       -- Below, we determine which case we're in and then insert the value at the end and continue
                       cont <- case addressNodeId `IMap.lookup` memoTable of
                                 Just oldVal                    -- Cache hit
                                   | val == oldVal -> return $ Left fArrayIndex   -- Case 1
                                   | True          -> return $ Right memoTable    -- Case 2

                                 Nothing           -> do        -- Cache miss

                                        let aInfo = (address, addressNodeId `Map.lookup` consts)

                                            -- NB. The order of modifications here is important as we
                                            -- keep the keys in ascending order. (Since we'll call fromAscList later on.)
                                            walk :: [(Int, SV)] -> [(Int, SV)] -> IO [(Int, SV)]
                                            walk []           sofar = return $ reverse sofar
                                            walk ((i, s):iss) sofar = modify i s >>= \s' -> walk iss ((i, s') : sofar)

                                            -- At the cached address i, currently storing value s. Conditionally update it to `b` (new value)
                                            -- if the addresses match. Otherwise keep it the same.
                                            modify :: Int -> SV -> IO SV
                                            modify i s = svToSV st $ svIte (svEqualWithConsts (nodeIdToSVal ak i, i `Map.lookup` consts) aInfo) b (swToSVal s)

                                        Right . IMap.fromAscList <$> walk (IMap.toAscList memoTable) []

                       case cont of
                         Left j   -> return j  -- There was a hit, and value was unchanged, nothing to do

                         Right mt -> do        -- There was a hit, and the value was different; or there was a miss. Insert the new value
                                               -- and create a new array. Note that we keep the aUi the same: Just because we modified
                                               -- an array, it doesn't mean we change the uninitialized reads: they still come from the same place.
                                               --
                                        newMemoTable <- R.newIORef $ IMap.insert addressNodeId val mt

                                        let j = FArrayIndex $ IMap.size fArrMap
                                            upd = IMap.insert (unFArrayIndex j) (aUi, newMemoTable)

                                        j `seq` modifyState st rFArrayMap upd (return ())
                                        return j

-- | Merge two given arrays on the symbolic condition
-- Intuitively: @mergeArrays cond a b = if cond then a else b@.
-- Merging pushes the if-then-else choice down on to elements
mergeSFunArr :: SVal -> SFunArr -> SFunArr -> SFunArr
mergeSFunArr t array1@(SFunArr ainfo@(sourceKind, targetKind) a) array2@(SFunArr binfo b)
  | ainfo /= binfo
  = error $ "Data.SBV.mergeSFunArr: Impossible happened, merging incompatbile arrays: " ++ show (ainfo, binfo)
  | Just test <- svAsBool t
  = if test then array1 else array2
  | True
  = SFunArr ainfo $ cache c
  where c st = do ai <- uncacheFAI a st
                  bi <- uncacheFAI b st

                  constMap <- R.readIORef (rconstMap st)
                  let consts = Map.fromList [(i, cv) | (cv, SV _ (NodeId i)) <- Map.toList constMap]

                  -- Catch the degenerate case of merging an array with itself. One
                  -- can argue this is pointless, but actually it comes up when one
                  -- is merging composite structures (through a Mergeable class instance)
                  -- that has an array component that didn't change. So, pays off in practice!
                  if unFArrayIndex ai == unFArrayIndex bi
                     then return ai  -- merging with itself, noop
                     else do fArrMap <- R.readIORef (rFArrayMap st)

                             case (unFArrayIndex ai `IMap.lookup` fArrMap, unFArrayIndex bi `IMap.lookup` fArrMap) of
                               (Nothing, _) -> error $ "Data.SBV.mergeSFunArr: Impossible happened while trying to access SFunArray, can't find index: " ++ show ai
                               (_, Nothing) -> error $ "Data.SBV.mergeSFunArr: Impossible happened while trying to access SFunArray, can't find index: " ++ show bi
                               (Just (aUi, raCache), Just (bUi, rbCache)) -> do

                                   -- This is where the complication happens. We need to merge the caches. If the same
                                   -- key appears in both, then that's the easy case: Just merge the entries. But if
                                   -- a key only appears in one but not the other? Just like in the read/write cases,
                                   -- we have to consider the possibility that the missing key can be any one of the
                                   -- other elements in the cache. So, for each non-matching key in either memo-table,
                                   -- we traverse the other and create a chain of look-up values.
                                   aMemo <- R.readIORef raCache
                                   bMemo <- R.readIORef rbCache

                                   let aMemoT = IMap.toAscList aMemo
                                       bMemoT = IMap.toAscList bMemo

                                       -- gen takes a uninitialized-read creator, a key, and the choices from the "other"
                                       -- cache that this key may map to. And creates a new SV that corresponds to the
                                       -- merged value:
                                       gen :: (SVal -> SVal) -> Int -> [(Int, SV)] -> IO SV
                                       gen mk k choices = svToSV st $ walk choices
                                         where kInfo = (nodeIdToSVal sourceKind k, k `Map.lookup` consts)

                                               walk :: [(Int, SV)] -> SVal
                                               walk []             = mk (fst kInfo)
                                               walk ((i, v) : ivs) = svIte (svEqualWithConsts (nodeIdToSVal sourceKind i, i `Map.lookup` consts) kInfo)
                                                                           (swToSVal v)
                                                                           (walk ivs)

                                       -- Insert into an existing map the new key value by merging according to the test
                                       fill :: Int -> SV -> SV -> IMap.IntMap SV -> IO (IMap.IntMap SV)
                                       fill k (SV _ (NodeId ni1)) (SV _ (NodeId ni2)) m = do v <- svToSV st (svIte t sval1 sval2)
                                                                                             return $ IMap.insert k v m
                                         where sval1 = nodeIdToSVal targetKind ni1
                                               sval2 = nodeIdToSVal targetKind ni2

                                       -- Walk down the memo-tables in tandem. If we find a common key: Simply fill it in. If we find
                                       -- a key only in one, generate the corresponding read from the other cache, and do the fill.
                                       merge []                  []                  sofar = return sofar
                                       merge ((k1, v1) : as)     []                  sofar = gen bUi k1 bMemoT >>= \v2  -> fill k1 v1  v2 sofar  >>= merge as []
                                       merge []                  ((k2, v2) : bs)     sofar = gen aUi k2 aMemoT >>= \v1  -> fill k2 v1  v2 sofar  >>= merge [] bs
                                       merge ass@((k1, v1) : as) bss@((k2, v2) : bs) sofar
                                         | k1 < k2                                         = gen bUi k1 bMemoT >>= \nv2 -> fill k1 v1  nv2 sofar >>= merge as  bss
                                         | k1 > k2                                         = gen aUi k2 aMemoT >>= \nv1 -> fill k2 nv1 v2  sofar >>= merge ass bs
                                         | True                                            =                               fill k1 v1  v2  sofar >>= merge as  bs

                                   mergedMap  <- merge aMemoT bMemoT IMap.empty
                                   memoMerged <- R.newIORef mergedMap

                                   -- Craft a new uninitializer. Note that we do *not* create a new initializer here,
                                   -- but simply merge the two initializers which will inherit their original unread
                                   -- references should the test be a constant.
                                   let mkUninitialized i = svIte t (aUi i) (bUi i)

                                   -- Add it to our collection:
                                   let j   = FArrayIndex $ IMap.size fArrMap
                                       upd = IMap.insert (unFArrayIndex j) (mkUninitialized, memoMerged)

                                   j `seq` modifyState st rFArrayMap upd (return ())

                                   return j

-- | Create a named new array
newSFunArr :: State -> (Kind, Kind) -> (Int -> String) -> Maybe SVal -> IO SFunArr
newSFunArr st (ak, bk) mkNm mbDef = do
        fArrMap <- R.readIORef (rFArrayMap st)
        memoTable <- R.newIORef IMap.empty

        let j  = FArrayIndex $ IMap.size fArrMap
            nm = mkNm (unFArrayIndex j)
            mkUninitialized i = case mbDef of
                                  Just def -> def
                                  _        -> svUninterpreted bk (nm ++ "_uninitializedRead") Nothing [i]

            upd = IMap.insert (unFArrayIndex j) (mkUninitialized, memoTable)

        registerLabel "SFunArray declaration" st nm
        j `seq` modifyState st rFArrayMap upd (return ())

        return $ SFunArr (ak, bk) $ cache $ const $ return j

--------------------------------------------------------------------------------
-- Utility functions

noUnint  :: (Maybe Int, String) -> a
noUnint x = error $ "Unexpected operation called on uninterpreted/enumerated value: " ++ show x

noUnint2 :: (Maybe Int, String) -> (Maybe Int, String) -> a
noUnint2 x y = error $ "Unexpected binary operation called on uninterpreted/enumerated values: " ++ show (x, y)

noCharLift :: Char -> a
noCharLift x = error $ "Unexpected operation called on char: " ++ show x

noStringLift :: String -> a
noStringLift x = error $ "Unexpected operation called on string: " ++ show x

noCharLift2 :: Char -> Char -> a
noCharLift2 x y = error $ "Unexpected binary operation called on chars: " ++ show (x, y)

noStringLift2 :: String -> String -> a
noStringLift2 x y = error $ "Unexpected binary operation called on strings: " ++ show (x, y)

liftSym1 :: (State -> Kind -> SV -> IO SV) -> (AlgReal -> AlgReal) -> (Integer -> Integer) -> (Float -> Float) -> (Double -> Double) -> SVal -> SVal
liftSym1 _   opCR opCI opCF opCD   (SVal k (Left a)) = SVal k . Left  $! mapCV opCR opCI opCF opCD noCharLift noStringLift noUnint a
liftSym1 opS _    _    _    _    a@(SVal k _)        = SVal k $ Right $ cache c
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

But this means that we have to grab the constant list for every symbolicly lifted operation, also do the
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

liftSym2 :: (State -> Kind -> SV -> SV -> IO SV) -> (CV -> CV -> Bool) -> (AlgReal -> AlgReal -> AlgReal) -> (Integer -> Integer -> Integer) -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> SVal -> SVal -> SVal
liftSym2 _   okCV opCR opCI opCF opCD   (SVal k (Left a)) (SVal _ (Left b)) | okCV a b = SVal k . Left  $! mapCV2 opCR opCI opCF opCD noCharLift2 noStringLift2 noUnint2 a b
liftSym2 opS _    _    _    _    _    a@(SVal k _)        b                            = SVal k $ Right $  liftSV2 opS k a b

liftSym2B :: (State -> Kind -> SV -> SV -> IO SV) -> (CV -> CV -> Bool) -> (AlgReal -> AlgReal -> Bool) -> (Integer -> Integer -> Bool) -> (Float -> Float -> Bool) -> (Double -> Double -> Bool) -> (Char -> Char -> Bool) -> (String -> String -> Bool) -> ([CVal] -> [CVal] -> Bool) -> ([CVal] -> [CVal] -> Bool) -> ((Maybe Int, String) -> (Maybe Int, String) -> Bool) -> SVal -> SVal -> SVal
liftSym2B _   okCV opCR opCI opCF opCD opCC opCS opCSeq opCTup opUI (SVal _ (Left a)) (SVal _ (Left b)) | okCV a b = svBool (liftCV2 opCR opCI opCF opCD opCC opCS opCSeq opCTup opUI a b)
liftSym2B opS _    _    _    _    _    _    _    _      _      _    a                 b                            = SVal KBool $ Right $ liftSV2 opS KBool a b

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

-- | eqOpt says the references are to the same SV, thus we can optimize. Note that
-- we explicitly disallow KFloat/KDouble here. Why? Because it's *NOT* true that
-- NaN == NaN, NaN >= NaN, and so-forth. So, we have to make sure we don't optimize
-- floats and doubles, in case the argument turns out to be NaN.
eqOpt :: SV -> SV -> SV -> Maybe SV
eqOpt w x y = case swKind x of
                KFloat  -> Nothing
                KDouble -> Nothing
                _       -> if x == y then Just w else Nothing

-- For uninterpreted/enumerated values, we carefully lift through the constructor index for comparisons:
uiLift :: String -> (Int -> Int -> Bool) -> (Maybe Int, String) -> (Maybe Int, String) -> Bool
uiLift _ cmp (Just i, _) (Just j, _) = i `cmp` j
uiLift w _   a           b           = error $ "Data.SBV.Core.Operations: Impossible happened while trying to lift " ++ w ++ " over " ++ show (a, b)

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
--
nonzeroCheck :: CV -> CV -> Bool
nonzeroCheck _ b = cvVal b /= CInteger 0

-- | Same as rationalCheck, except for SBV's
rationalSBVCheck :: SVal -> SVal -> Bool
rationalSBVCheck (SVal KReal (Left a)) (SVal KReal (Left b)) = rationalCheck a b
rationalSBVCheck _                     _                     = True

noReal :: String -> AlgReal -> AlgReal -> AlgReal
noReal o a b = error $ "SBV.AlgReal." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noFloat :: String -> Float -> Float -> Float
noFloat o a b = error $ "SBV.Float." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noDouble :: String -> Double -> Double -> Double
noDouble o a b = error $ "SBV.Double." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noRealUnary :: String -> AlgReal -> AlgReal
noRealUnary o a = error $ "SBV.AlgReal." ++ o ++ ": Unexpected argument: " ++ show a

noFloatUnary :: String -> Float -> Float
noFloatUnary o a = error $ "SBV.Float." ++ o ++ ": Unexpected argument: " ++ show a

noDoubleUnary :: String -> Double -> Double
noDoubleUnary o a = error $ "SBV.Double." ++ o ++ ": Unexpected argument: " ++ show a

{-# ANN svIte     ("HLint: ignore Eta reduce" :: String)         #-}
{-# ANN svLazyIte ("HLint: ignore Eta reduce" :: String)         #-}
{-# ANN module    ("HLint: ignore Reduce duplication" :: String) #-}
