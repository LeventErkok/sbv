-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Operations
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Constructors and basic operations on symbolic values
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.Operations
  (
  -- ** Basic constructors
    svTrue, svFalse, svBool
  , svInteger, svFloat, svDouble, svReal
  -- ** Basic destructors
  , svAsBool, svAsInteger, svNumerator, svDenominator
  -- ** Basic operations
  , svPlus, svTimes, svMinus, svUNeg, svAbs
  , svDivide, svQuot, svRem
  , svEqual, svNotEqual
  , svLessThan, svGreaterThan, svLessEq, svGreaterEq
  , svAnd, svOr, svXOr, svNot
  , svShl, svShr, svRol, svRor
  , svExtract, svJoin
  , svUninterpreted
  , svIte, svLazyIte, svSymbolicMerge
  , svSelect
  , svSign, svUnsign
  -- ** Derived operations
  , svToWord1, svFromWord1, svTestBit
  , svShiftLeft, svShiftRight
  , svRotateLeft, svRotateRight
  )
  where

import Data.Bits (Bits(..))
import Data.List (genericIndex, genericLength, genericTake)

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Kind
import Data.SBV.BitVectors.Concrete
import Data.SBV.BitVectors.Symbolic

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
svInteger k n = SVal k (Left (mkConstCW k n))

-- | Convert from a Float
svFloat :: Float -> SVal
svFloat f = SVal KFloat (Left (CW KFloat (CWFloat f)))

-- | Convert from a Float
svDouble :: Double -> SVal
svDouble d = SVal KDouble (Left (CW KDouble (CWDouble d)))

-- | Convert from a Rational
svReal :: Rational -> SVal
svReal d = SVal KReal (Left (CW KReal (CWAlgReal (fromRational d))))


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

--------------------------------------------------------------------------------
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
svDivide = liftSym2 (mkSymOp Quot) rationalCheck (/) die (/) (/)
   where -- should never happen
         die = error "impossible: integer valued data found in Fractional instance"

-- | Quotient: Overloaded operation whose meaning depends on the kind at which
-- it is used: For unbounded integers, it corresponds to the SMT-Lib
-- "div" operator ("Euclidean" division, which always has a
-- non-negative remainder). For unsigned bitvectors, it is "bvudiv";
-- and for signed bitvectors it is "bvsdiv", which rounds toward zero.
-- All operations have unspecified semantics in case @y = 0@.
svQuot :: SVal -> SVal -> SVal
svQuot x y
  | isConcreteZero x = x
  | isConcreteOne y  = x
  | True             = liftSym2 (mkSymOp Quot) nonzeroCheck
                                (noReal "quot") quot' (noFloat "quot") (noDouble "quot") x y
  where
    quot' a b | kindOf x == KUnbounded = div a (abs b) * signum b
              | otherwise              = quot a b

-- | Remainder: Overloaded operation whose meaning depends on the kind at which
-- it is used: For unbounded integers, it corresponds to the SMT-Lib
-- "mod" operator (always non-negative). For unsigned bitvectors, it
-- is "bvurem"; and for signed bitvectors it is "bvsrem", which rounds
-- toward zero (sign of remainder matches that of @x@). All operations
-- have unspecified semantics in case @y = 0@.
svRem :: SVal -> SVal -> SVal
svRem x y
  | isConcreteZero x = x
  | isConcreteOne y  = svInteger (kindOf x) 0
  | True             = liftSym2 (mkSymOp Rem) nonzeroCheck
                                (noReal "rem") rem' (noFloat "rem") (noDouble "rem") x y
  where
    rem' a b | kindOf x == KUnbounded = mod a (abs b)
             | otherwise              = rem a b

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
svEqual = liftSym2B (mkSymOpSC (eqOptBool Equal trueSW) Equal) rationalCheck (==) (==) (==) (==) (==)

-- | Inequality.
svNotEqual :: SVal -> SVal -> SVal
svNotEqual = liftSym2B (mkSymOpSC (eqOptBool NotEqual falseSW) NotEqual) rationalCheck (/=) (/=) (/=) (/=) (/=)

-- | Less than.
svLessThan :: SVal -> SVal -> SVal
svLessThan x y
  | isConcreteMax x = svFalse
  | isConcreteMin y = svFalse
  | True            = liftSym2B (mkSymOpSC (eqOpt falseSW) LessThan) rationalCheck (<) (<) (<) (<) (uiLift "<" (<)) x y

-- | Greater than.
svGreaterThan :: SVal -> SVal -> SVal
svGreaterThan x y
  | isConcreteMin x = svFalse
  | isConcreteMax y = svFalse
  | True            = liftSym2B (mkSymOpSC (eqOpt falseSW) GreaterThan) rationalCheck (>) (>) (>) (>) (uiLift ">"  (>)) x y

-- | Less than or equal to.
svLessEq :: SVal -> SVal -> SVal
svLessEq x y
  | isConcreteMin x = svTrue
  | isConcreteMax y = svTrue
  | True            = liftSym2B (mkSymOpSC (eqOpt trueSW) LessEq) rationalCheck (<=) (<=) (<=) (<=) (uiLift "<=" (<=)) x y

-- | Greater than or equal to.
svGreaterEq :: SVal -> SVal -> SVal
svGreaterEq x y
  | isConcreteMax x = svTrue
  | isConcreteMin y = svTrue
  | True            = liftSym2B (mkSymOpSC (eqOpt trueSW) GreaterEq) rationalCheck (>=) (>=) (>=) (>=) (uiLift ">=" (>=)) x y

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
  | i < 0   = svShr x (-i)
  | i == 0  = x
  | True    = liftSym1 (mkSymOp1 (Shl i))
                       (noRealUnary "shiftL") (`shiftL` i)
                       (noFloatUnary "shiftL") (noDoubleUnary "shiftL") x

-- | Shift right by a constant amount. Translates to either "bvlshr"
-- (logical shift right) or "bvashr" (arithmetic shift right) in
-- SMT-Lib, depending on whether @x@ is a signed bitvector.
svShr :: SVal -> Int -> SVal
svShr x i
  | i < 0   = svShl x (-i)
  | i == 0  = x
  | True    = liftSym1 (mkSymOp1 (Shr i))
                       (noRealUnary "shiftR") (`shiftR` i)
                       (noFloatUnary "shiftR") (noDoubleUnary "shiftR") x

-- | Rotate-left, by a constant
svRol :: SVal -> Int -> SVal
svRol x i
  | i < 0   = svRor x (-i)
  | i == 0  = x
  | True    = case kindOf x of
                KBounded _ sz -> liftSym1 (mkSymOp1 (Rol (i `mod` sz)))
                                          (noRealUnary "rotateL") (rot True sz i)
                                          (noFloatUnary "rotateL") (noDoubleUnary "rotateL") x
                _ -> svShl x i   -- for unbounded Integers, rotateL is the same as shiftL in Haskell

-- | Rotate-right, by a constant
svRor :: SVal -> Int -> SVal
svRor x i
  | i < 0   = svRol x (-i)
  | i == 0  = x
  | True    = case kindOf x of
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
  = SVal k (Left (CW k (CWInteger 0)))
  | SVal _ (Left (CW _ (CWInteger v))) <- x
  = SVal k (Left (normCW (CW k (CWInteger (v `shiftR` j)))))
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
  = SVal k (Left (CW k (CWInteger (m `shiftL` j .|. n))))
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
  | force, rationalSBVCheck a b, areConcretelyEqual a b
  = a
  | True
  = SVal k $ Right $ cache c
  where c st = do swt <- svToSW st t
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
-- The shift amount must be an unsigned quantity.
svShiftLeft :: SVal -> SVal -> SVal
svShiftLeft x i
  | hasSign i = error "sShiftLeft: shift amount should be unsigned"
  | True      = svSelect [svShl x k | k <- [0 .. intSizeOf x - 1]] z i
  where z = svInteger (kindOf x) 0

-- | Generalization of 'svShr', where the shift-amount is symbolic.
-- The shift amount must be an unsigned quantity.
--
-- NB. If the shiftee is signed, then this is an arithmetic shift;
-- otherwise it's logical.
svShiftRight :: SVal -> SVal -> SVal
svShiftRight x i
  | hasSign i = error "sShiftRight: shift amount should be unsigned"
  | True      = svSelect [svShr x k | k <- [0 .. intSizeOf x - 1]] z i
  where z = svInteger (kindOf x) 0

-- | Generalization of 'svRol', where the rotation amount is symbolic.
-- The rotation amount must be an unsigned quantity.
svRotateLeft :: SVal -> SVal -> SVal
svRotateLeft x i
  | hasSign i              = error "sRotateLeft: rotation amount should be unsigned"
  | bit si <= toInteger sx = svSelect [x `svRol` k | k <- [0 .. bit si - 1]] z i         -- wrap-around not possible
  | True                   = svSelect [x `svRol` k | k <- [0 .. sx     - 1]] z (i `svRem` n)
    where sx = intSizeOf x
          si = intSizeOf i
          z = svInteger (kindOf x) 0
          n = svInteger (kindOf i) (toInteger sx)

-- | Generalization of 'svRor', where the rotation amount is symbolic.
-- The rotation amount must be an unsigned quantity.
svRotateRight :: SVal -> SVal -> SVal
svRotateRight x i
  | hasSign i              = error "sRotateRight: rotation amount should be unsigned"
  | bit si <= toInteger sx = svSelect [x `svRor` k | k <- [0 .. bit si - 1]] z i         -- wrap-around not possible
  | True                   = svSelect [x `svRor` k | k <- [0 .. sx     - 1]] z (i `svRem` n)
    where sx = intSizeOf x
          si = intSizeOf i
          z = svInteger (kindOf x) 0
          n = svInteger (kindOf i) (toInteger sx)


--------------------------------------------------------------------------------
-- Utility functions

noUnint  :: (Maybe Int, String) -> a
noUnint x = error $ "Unexpected operation called on uninterpreted/enumerated value: " ++ show x

noUnint2 :: (Maybe Int, String) -> (Maybe Int, String) -> a
noUnint2 x y = error $ "Unexpected binary operation called on uninterpreted/enumerated values: " ++ show (x, y)

liftSym1 :: (State -> Kind -> SW -> IO SW) -> (AlgReal -> AlgReal) -> (Integer -> Integer) -> (Float -> Float) -> (Double -> Double) -> SVal -> SVal
liftSym1 _   opCR opCI opCF opCD   (SVal k (Left a)) = SVal k $ Left  $ mapCW opCR opCI opCF opCD noUnint a
liftSym1 opS _    _    _    _    a@(SVal k _)        = SVal k $ Right $ cache c
   where c st = do swa <- svToSW st a
                   opS st k swa

liftSW2 :: (State -> Kind -> SW -> SW -> IO SW) -> Kind -> SVal -> SVal -> Cached SW
liftSW2 opS k a b = cache c
  where c st = do sw1 <- svToSW st a
                  sw2 <- svToSW st b
                  opS st k sw1 sw2

liftSym2 :: (State -> Kind -> SW -> SW -> IO SW) -> (CW -> CW -> Bool) -> (AlgReal -> AlgReal -> AlgReal) -> (Integer -> Integer -> Integer) -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> SVal -> SVal -> SVal
liftSym2 _   okCW opCR opCI opCF opCD   (SVal k (Left a)) (SVal _ (Left b)) | okCW a b = SVal k $ Left  $ mapCW2 opCR opCI opCF opCD noUnint2 a b
liftSym2 opS _    _    _    _    _    a@(SVal k _)        b                            = SVal k $ Right $ liftSW2 opS k a b

liftSym2B :: (State -> Kind -> SW -> SW -> IO SW) -> (CW -> CW -> Bool) -> (AlgReal -> AlgReal -> Bool) -> (Integer -> Integer -> Bool) -> (Float -> Float -> Bool) -> (Double -> Double -> Bool) -> ((Maybe Int, String) -> (Maybe Int, String) -> Bool) -> SVal -> SVal -> SVal
liftSym2B _   okCW opCR opCI opCF opCD opUI (SVal _ (Left a)) (SVal _ (Left b)) | okCW a b = svBool (liftCW2 opCR opCI opCF opCD opUI a b)
liftSym2B opS _    _    _    _    _    _    a                 b                            = SVal KBool $ Right $ liftSW2 opS KBool a b

mkSymOpSC :: (SW -> SW -> Maybe SW) -> Op -> State -> Kind -> SW -> SW -> IO SW
mkSymOpSC shortCut op st k a b = maybe (newExpr st k (SBVApp op [a, b])) return (shortCut a b)

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
uiLift w _   a           b           = error $ "Data.SBV.BitVectors.Model: Impossible happened while trying to lift " ++ w ++ " over " ++ show (a, b)

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

-- | Predicate for optimizing conditionals.
areConcretelyEqual :: SVal -> SVal -> Bool
areConcretelyEqual (SVal _ (Left a)) (SVal _ (Left b)) = a == b
areConcretelyEqual _                       _           = False

-- | Most operations on concrete rationals require a compatibility check to avoid faulting
-- on algebraic reals.
rationalCheck :: CW -> CW -> Bool
rationalCheck a b = case (cwVal a, cwVal b) of
                     (CWAlgReal x, CWAlgReal y) -> isExactRational x && isExactRational y
                     _                          -> True

-- | Quot/Rem operations require a nonzero check on the divisor.
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
