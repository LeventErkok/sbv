-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Operations
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
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
  , svUninterpreted
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
  -- Utils
  , mkSymOp
  )
  where

import Data.Bits (Bits(..))
import Data.List (genericIndex, genericLength, genericTake)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic

import Data.Ratio

--------------------------------------------------------------------------------
-- Basic constructors

-- | Boolean True.
svTrue :: SVal
svTrue = SVal KBool (Left trueCW)

-- | Boolean False.
svFalse :: SVal
svFalse = SVal KBool (Left falseCW)

-- | Convert from a Boolean.
svBool :: Bool -> SVal
svBool b = if b then svTrue else svFalse

-- | Convert from an Integer.
svInteger :: Kind -> Integer -> SVal
svInteger k n = SVal k (Left $! mkConstCW k n)

-- | Convert from a Float
svFloat :: Float -> SVal
svFloat f = SVal KFloat (Left $! CW KFloat (CWFloat f))

-- | Convert from a Float
svDouble :: Double -> SVal
svDouble d = SVal KDouble (Left $! CW KDouble (CWDouble d))

-- | Convert from a String
svString :: String -> SVal
svString s = SVal KString (Left $! CW KString (CWString s))

-- | Convert from a Char
svChar :: Char -> SVal
svChar c = SVal KChar (Left $! CW KChar (CWChar c))

-- | Convert from a Rational
svReal :: Rational -> SVal
svReal d = SVal KReal (Left $! CW KReal (CWAlgReal (fromRational d)))

--------------------------------------------------------------------------------
-- Basic destructors

-- | Extract a bool, by properly interpreting the integer stored.
svAsBool :: SVal -> Maybe Bool
svAsBool (SVal _ (Left cw)) = Just (cwToBool cw)
svAsBool _                  = Nothing

-- | Extract an integer from a concrete value.
svAsInteger :: SVal -> Maybe Integer
svAsInteger (SVal _ (Left (CW _ (CWInteger n)))) = Just n
svAsInteger _                                    = Nothing

-- | Grab the numerator of an SReal, if available
svNumerator :: SVal -> Maybe Integer
svNumerator (SVal KReal (Left (CW KReal (CWAlgReal (AlgRational True r))))) = Just $ numerator r
svNumerator _                                                               = Nothing

-- | Grab the denominator of an SReal, if available
svDenominator :: SVal -> Maybe Integer
svDenominator (SVal KReal (Left (CW KReal (CWAlgReal (AlgRational True r))))) = Just $ denominator r
svDenominator _                                                               = Nothing

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
eqOptBool :: Op -> SW -> SW -> SW -> Maybe SW
eqOptBool op w x y
  | k == KBool && op == Equal    && x == trueSW  = Just y         -- true  .== y     --> y
  | k == KBool && op == Equal    && y == trueSW  = Just x         -- x     .== true  --> x
  | k == KBool && op == NotEqual && x == falseSW = Just y         -- false ./= y     --> y
  | k == KBool && op == NotEqual && y == falseSW = Just x         -- x     ./= false --> x
  | True                                         = eqOpt w x y    -- fallback
  where k = swKind x

-- | Equality.
svEqual :: SVal -> SVal -> SVal
svEqual = liftSym2B (mkSymOpSC (eqOptBool Equal trueSW) Equal) rationalCheck (==) (==) (==) (==) (==) (==) (==)

-- | Inequality.
svNotEqual :: SVal -> SVal -> SVal
svNotEqual = liftSym2B (mkSymOpSC (eqOptBool NotEqual falseSW) NotEqual) rationalCheck (/=) (/=) (/=) (/=) (/=) (/=) (/=)

-- | Less than.
svLessThan :: SVal -> SVal -> SVal
svLessThan x y
  | isConcreteMax x = svFalse
  | isConcreteMin y = svFalse
  | True            = liftSym2B (mkSymOpSC (eqOpt falseSW) LessThan) rationalCheck (<) (<) (<) (<) (<) (<) (uiLift "<" (<)) x y

-- | Greater than.
svGreaterThan :: SVal -> SVal -> SVal
svGreaterThan x y
  | isConcreteMin x = svFalse
  | isConcreteMax y = svFalse
  | True            = liftSym2B (mkSymOpSC (eqOpt falseSW) GreaterThan) rationalCheck (>) (>) (>) (>) (>) (>) (uiLift ">"  (>)) x y

-- | Less than or equal to.
svLessEq :: SVal -> SVal -> SVal
svLessEq x y
  | isConcreteMin x = svTrue
  | isConcreteMax y = svTrue
  | True            = liftSym2B (mkSymOpSC (eqOpt trueSW) LessEq) rationalCheck (<=) (<=) (<=) (<=) (<=) (<=) (uiLift "<=" (<=)) x y

-- | Greater than or equal to.
svGreaterEq :: SVal -> SVal -> SVal
svGreaterEq x y
  | isConcreteMax x = svTrue
  | isConcreteMin y = svTrue
  | True            = liftSym2B (mkSymOpSC (eqOpt trueSW) GreaterEq) rationalCheck (>=) (>=) (>=) (>=) (>=) (>=) (uiLift ">=" (>=)) x y

-- | Bitwise and.
svAnd :: SVal -> SVal -> SVal
svAnd x y
  | isConcreteZero x = x
  | isConcreteOnes x = y
  | isConcreteZero y = y
  | isConcreteOnes y = x
  | True             = liftSym2 (mkSymOpSC opt And) (const (const True)) (noReal ".&.") (.&.) (noFloat ".&.") (noDouble ".&.") x y
  where opt a b
          | a == falseSW || b == falseSW = Just falseSW
          | a == trueSW                  = Just b
          | b == trueSW                  = Just a
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
          | a == trueSW || b == trueSW = Just trueSW
          | a == falseSW               = Just b
          | b == falseSW               = Just a
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
          | a == b && swKind a == KBool = Just falseSW
          | a == falseSW                = Just b
          | b == falseSW                = Just a
          | True                        = Nothing

-- | Bitwise complement.
svNot :: SVal -> SVal
svNot = liftSym1 (mkSymOp1SC opt Not)
                 (noRealUnary "complement") complement
                 (noFloatUnary "complement") (noDoubleUnary "complement")
  where opt a
          | a == falseSW = Just trueSW
          | a == trueSW  = Just falseSW
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
  = SVal k (Left $! CW k (CWInteger 0))
  | SVal _ (Left (CW _ (CWInteger v))) <- x
  = SVal k (Left $! normCW (CW k (CWInteger (v `shiftR` j))))
  | True
  = SVal k (Right (cache y))
  where k = KBounded s (i - j + 1)
        y st = do sw <- svToSW st x
                  newExpr st k (SBVApp (Extract i j) [sw])
svExtract _ _ _ = error "extract: non-bitvector type"

-- | Join two words, by concataneting
svJoin :: SVal -> SVal -> SVal
svJoin x@(SVal (KBounded s i) a) y@(SVal (KBounded _ j) b)
  | i == 0 = y
  | j == 0 = x
  | Left (CW _ (CWInteger m)) <- a, Left (CW _ (CWInteger n)) <- b
  = SVal k (Left $! CW k (CWInteger (m `shiftL` j .|. n)))
  | True
  = SVal k (Right (cache z))
  where
    k = KBounded s (i + j)
    z st = do xsw <- svToSW st x
              ysw <- svToSW st y
              newExpr st k (SBVApp Join [xsw, ysw])
svJoin _ _ = error "svJoin: non-bitvector type"

-- | Uninterpreted constants and functions. An uninterpreted constant is
-- a value that is indexed by its name. The only property the prover assumes
-- about these values are that they are equivalent to themselves; i.e., (for
-- functions) they return the same results when applied to same arguments.
-- We support uninterpreted-functions as a general means of black-box'ing
-- operations that are /irrelevant/ for the purposes of the proof; i.e., when
-- the proofs can be performed without any knowledge about the function itself.
svUninterpreted :: Kind -> String -> Maybe [String] -> [SVal] -> SVal
svUninterpreted k nm code args = SVal k $ Right $ cache result
  where result st = do let ty = SBVType (map kindOf args ++ [k])
                       newUninterpreted st nm ty code
                       sws <- mapM (svToSW st) args
                       mapM_ forceSWArg sws
                       newExpr st k $ SBVApp (Uninterpreted nm) sws

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

        c st = do swt <- svToSW st t
                  case () of
                    () | swt == trueSW  -> svToSW st a       -- these two cases should never be needed as we expect symbolicMerge to be
                    () | swt == falseSW -> svToSW st b       -- called with symbolic tests, but just in case..
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
                                like to share 'k', which would evaluate (correctly) to 'x' under the given assumption. When we backtrack and evaluate the 'else'
                                branch of the first ite, we'd see 'k' is needed again, and we'd look it up from our sharing map to find (incorrectly) that its value
                                is 'x', which was stored there under the assumption that y was 0, which no longer holds. Clearly, this is unsound.

                                A sound implementation would have to precisely track which assumptions were active at the time expressions get shared. That is,
                                in the above example, we should record that the value of 'k' was cached under the assumption that 'y' is 0. While sound, this
                                approach unfortunately leads to significant loss of valid sharing when the value itself had nothing to do with the assumption itself.
                                To wit, consider:

                                   foo x y = ite (y .== 0) k (k+1)
                                     where k = x+5

                                If we tracked the assumptions, we would recompute 'k' twice, since the branch assumptions would differ. Clearly, there is no need to
                                re-compute 'k' in this case since its value is independent of y. Note that the whole SBV performance story is based on agressive sharing,
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
                             swa <- svToSW sta a -- evaluate 'then' branch
                             swb <- svToSW stb b -- evaluate 'else' branch
                             case () of               -- merge:
                               () | swa == swb                      -> return swa
                               () | swa == trueSW && swb == falseSW -> return swt
                               () | swa == falseSW && swb == trueSW -> newExpr st k (SBVApp Not [swt])
                               ()                                   -> newExpr st k (SBVApp Ite [swt, swa, swb])

-- | Total indexing operation. @svSelect xs default index@ is
-- intuitively the same as @xs !! index@, except it evaluates to
-- @default@ if @index@ overflows. Translates to SMT-Lib tables.
svSelect :: [SVal] -> SVal -> SVal -> SVal
svSelect xs err ind
  | SVal _ (Left c) <- ind =
    case cwVal c of
      CWInteger i -> if i < 0 || i >= genericLength xs
                     then err
                     else xs `genericIndex` i
      _           -> error $ "SBV.select: unsupported " ++ show (kindOf ind) ++ " valued select/index expression"
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
    r st = do sws <- mapM (svToSW st) xs
              swe <- svToSW st err
              if all (== swe) sws  -- off-chance that all elts are the same
                 then return swe
                 else do idx <- getTableIndex st kInd kElt sws
                         swi <- svToSW st ind
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
    y st = do xsw <- svToSW st x
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
        y st   = do xsw <- svToSW st x
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
          = Just $ SVal kx . Left $! normCW $ CW kx (CWInteger (xv `opC` shiftAmount iv))

          | isInteger x || isInteger i
          = bailOut $ "Not yet implemented unbounded/non-constants shifts for " ++ show (kx, ki) ++ ", please file a request!"

          | not (isBounded x && isBounded i)
          = bailOut $ "Unexpected kinds: " ++ show (kx, ki)

          | True
          = Nothing

          where bailOut m = error $ "SBV." ++ nm ++ ": " ++ m

                getConst (SVal _ (Left (CW _ (CWInteger val)))) = Just val
                getConst _                                      = Nothing

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
        -- overflow. See https://github.com/LeventErkok/sbv/issues/323 for this case. Thus, we
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
           where result st = do sw1 <- svToSW st x
                                sw2 <- svToSW st i

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
    where r st = do sx <- svToSW st x
                    sy <- svToSW st y
                    newExpr st KBool $ SBVApp (OverflowOp o) [sx, sy]

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

liftSym1 :: (State -> Kind -> SW -> IO SW) -> (AlgReal -> AlgReal) -> (Integer -> Integer) -> (Float -> Float) -> (Double -> Double) -> SVal -> SVal
liftSym1 _   opCR opCI opCF opCD   (SVal k (Left a)) = SVal k . Left  $! mapCW opCR opCI opCF opCD noCharLift noStringLift noUnint a
liftSym1 opS _    _    _    _    a@(SVal k _)        = SVal k $ Right $ cache c
   where c st = do swa <- svToSW st a
                   opS st k swa

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
happens after we start computing the if-then-else, hence we are already committed to an SW at that point. The call
to ite eventually recognizes this, but at that point it picks up the now constants from SW's, missing the constant
folding opportunity.

We can fix this, by looking up the constants table in liftSW2, like this:


    liftSW2 :: (CW -> CW -> Bool) -> (CW -> CW -> CW) -> (State -> Kind -> SW -> SW -> IO SW) -> Kind -> SVal -> SVal -> Cached SW
    liftSW2 okCW opCW opS k a b = cache c
      where c st = do sw1 <- svToSW st a
                      sw2 <- svToSW st b
                      cmap <- readIORef (rconstMap st)
                      let cw1  = [cw | ((_, cw), sw) <- M.toList cmap, sw == sw1]
                          cw2  = [cw | ((_, cw), sw) <- M.toList cmap, sw == sw2]
                      case (cw1, cw2) of
                        ([x], [y]) | okCW x y -> newConst st $ opCW x y
                        _                     -> opS st k sw1 sw2

(with obvious modifications to call sites to get the proper arguments.)

But this means that we have to grab the constant list for every symbolicly lifted operation, also do the
same for other places, etc.; for the rare opportunity of catching a @x .== x@ optimization. Even then, the
constants for the branches would still be generated. (i.e., in the above example we would still generate
@s1@ and @s2@, but would skip @s3@.)

It seems to me that the price to pay is rather high, as this is hardly the most common case; so we're opting
here to ignore these cases.

See https://github.com/LeventErkok/sbv/issues/379 for some further discussion.
-}
liftSW2 :: (State -> Kind -> SW -> SW -> IO SW) -> Kind -> SVal -> SVal -> Cached SW
liftSW2 opS k a b = cache c
  where c st = do sw1 <- svToSW st a
                  sw2 <- svToSW st b
                  opS st k sw1 sw2

liftSym2 :: (State -> Kind -> SW -> SW -> IO SW) -> (CW -> CW -> Bool) -> (AlgReal -> AlgReal -> AlgReal) -> (Integer -> Integer -> Integer) -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> SVal -> SVal -> SVal
liftSym2 _   okCW opCR opCI opCF opCD   (SVal k (Left a)) (SVal _ (Left b)) | okCW a b = SVal k . Left  $! mapCW2 opCR opCI opCF opCD noCharLift2 noStringLift2 noUnint2 a b
liftSym2 opS _    _    _    _    _    a@(SVal k _)        b                            = SVal k $ Right $  liftSW2 opS k a b

liftSym2B :: (State -> Kind -> SW -> SW -> IO SW) -> (CW -> CW -> Bool) -> (AlgReal -> AlgReal -> Bool) -> (Integer -> Integer -> Bool) -> (Float -> Float -> Bool) -> (Double -> Double -> Bool) -> (Char -> Char -> Bool) -> (String -> String -> Bool) -> ((Maybe Int, String) -> (Maybe Int, String) -> Bool) -> SVal -> SVal -> SVal
liftSym2B _   okCW opCR opCI opCF opCD opCC opCS opUI (SVal _ (Left a)) (SVal _ (Left b)) | okCW a b = svBool (liftCW2 opCR opCI opCF opCD opCC opCS opUI a b)
liftSym2B opS _    _    _    _    _    _    _    _    a                 b                            = SVal KBool $ Right $ liftSW2 opS KBool a b

-- | Create a symbolic two argument operation; with shortcut optimizations
mkSymOpSC :: (SW -> SW -> Maybe SW) -> Op -> State -> Kind -> SW -> SW -> IO SW
mkSymOpSC shortCut op st k a b = maybe (newExpr st k (SBVApp op [a, b])) return (shortCut a b)

-- | Create a symbolic two argument operation; no shortcut optimizations
mkSymOp :: Op -> State -> Kind -> SW -> SW -> IO SW
mkSymOp = mkSymOpSC (const (const Nothing))

mkSymOp1SC :: (SW -> Maybe SW) -> Op -> State -> Kind -> SW -> IO SW
mkSymOp1SC shortCut op st k a = maybe (newExpr st k (SBVApp op [a])) return (shortCut a)

mkSymOp1 :: Op -> State -> Kind -> SW -> IO SW
mkSymOp1 = mkSymOp1SC (const Nothing)

-- | eqOpt says the references are to the same SW, thus we can optimize. Note that
-- we explicitly disallow KFloat/KDouble here. Why? Because it's *NOT* true that
-- NaN == NaN, NaN >= NaN, and so-forth. So, we have to make sure we don't optimize
-- floats and doubles, in case the argument turns out to be NaN.
eqOpt :: SW -> SW -> SW -> Maybe SW
eqOpt w x y = case swKind x of
                KFloat  -> Nothing
                KDouble -> Nothing
                _       -> if x == y then Just w else Nothing

-- For uninterpreted/enumerated values, we carefully lift through the constructor index for comparisons:
uiLift :: String -> (Int -> Int -> Bool) -> (Maybe Int, String) -> (Maybe Int, String) -> Bool
uiLift _ cmp (Just i, _) (Just j, _) = i `cmp` j
uiLift w _   a           b           = error $ "Data.SBV.Core.Operations: Impossible happened while trying to lift " ++ w ++ " over " ++ show (a, b)

-- | Predicate for optimizing word operations like (+) and (*).
isConcreteZero :: SVal -> Bool
isConcreteZero (SVal _     (Left (CW _     (CWInteger n)))) = n == 0
isConcreteZero (SVal KReal (Left (CW KReal (CWAlgReal v)))) = isExactRational v && v == 0
isConcreteZero _                                            = False

-- | Predicate for optimizing word operations like (+) and (*).
isConcreteOne :: SVal -> Bool
isConcreteOne (SVal _     (Left (CW _     (CWInteger 1)))) = True
isConcreteOne (SVal KReal (Left (CW KReal (CWAlgReal v)))) = isExactRational v && v == 1
isConcreteOne _                                            = False

-- | Predicate for optimizing bitwise operations.
isConcreteOnes :: SVal -> Bool
isConcreteOnes (SVal _ (Left (CW (KBounded b w) (CWInteger n)))) = n == if b then -1 else bit w - 1
isConcreteOnes (SVal _ (Left (CW KUnbounded     (CWInteger n)))) = n == -1
isConcreteOnes (SVal _ (Left (CW KBool          (CWInteger n)))) = n == 1
isConcreteOnes _                                                 = False

-- | Predicate for optimizing comparisons.
isConcreteMax :: SVal -> Bool
isConcreteMax (SVal _ (Left (CW (KBounded False w) (CWInteger n)))) = n == bit w - 1
isConcreteMax (SVal _ (Left (CW (KBounded True  w) (CWInteger n)))) = n == bit (w - 1) - 1
isConcreteMax (SVal _ (Left (CW KBool              (CWInteger n)))) = n == 1
isConcreteMax _                                                     = False

-- | Predicate for optimizing comparisons.
isConcreteMin :: SVal -> Bool
isConcreteMin (SVal _ (Left (CW (KBounded False _) (CWInteger n)))) = n == 0
isConcreteMin (SVal _ (Left (CW (KBounded True  w) (CWInteger n)))) = n == - bit (w - 1)
isConcreteMin (SVal _ (Left (CW KBool              (CWInteger n)))) = n == 0
isConcreteMin _                                                     = False

-- | Most operations on concrete rationals require a compatibility check to avoid faulting
-- on algebraic reals.
rationalCheck :: CW -> CW -> Bool
rationalCheck a b = case (cwVal a, cwVal b) of
                     (CWAlgReal x, CWAlgReal y) -> isExactRational x && isExactRational y
                     _                          -> True

-- | Quot/Rem operations require a nonzero check on the divisor.
--
nonzeroCheck :: CW -> CW -> Bool
nonzeroCheck _ b = cwVal b /= CWInteger 0

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
