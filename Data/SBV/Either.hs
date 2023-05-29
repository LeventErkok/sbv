-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Either
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic coproduct, symbolic version of Haskell's 'Either' type.
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Either (
    -- * Constructing sums
      sLeft, sRight, liftEither
    -- * Destructing sums
    , either
    -- * Mapping functions
    , bimap, first, second
    -- * Scrutinizing branches of a sum
    , isLeft, isRight, fromLeft, fromRight
  ) where

import           Prelude hiding (either)
import qualified Prelude

import Data.Proxy (Proxy(Proxy))

import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Prelude hiding(either)
-- >>> import Data.SBV

-- | Construct an @SEither a b@ from an @SBV a@
--
-- >>> sLeft 3 :: SEither Integer Bool
-- Left 3 :: SEither Integer Bool
sLeft :: forall a b. (SymVal a, SymVal b) => SBV a -> SEither a b
sLeft sa
  | Just a <- unliteral sa
  = literal (Left a)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k1 = kindOf (Proxy @a)
        k2 = kindOf (Proxy @b)
        k  = KEither k1 k2

        res st = do asv <- sbvToSV st sa
                    newExpr st k $ SBVApp (EitherConstructor k1 k2 False) [asv]

-- | Return 'sTrue' if the given symbolic value is 'Left', 'sFalse' otherwise
--
-- >>> isLeft (sLeft 3 :: SEither Integer Bool)
-- True
-- >>> isLeft (sRight sTrue :: SEither Integer Bool)
-- False
isLeft :: (SymVal a, SymVal b) => SEither a b -> SBV Bool
isLeft = either (const sTrue) (const sFalse)

-- | Construct an @SEither a b@ from an @SBV b@
--
-- >>> sRight sFalse :: SEither Integer Bool
-- Right False :: SEither Integer Bool
sRight :: forall a b. (SymVal a, SymVal b) => SBV b -> SEither a b
sRight sb
  | Just b <- unliteral sb
  = literal (Right b)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k1 = kindOf (Proxy @a)
        k2 = kindOf (Proxy @b)
        k  = KEither k1 k2

        res st = do bsv <- sbvToSV st sb
                    newExpr st k $ SBVApp (EitherConstructor k1 k2 True) [bsv]

-- | Return 'sTrue' if the given symbolic value is 'Right', 'sFalse' otherwise
--
-- >>> isRight (sLeft 3 :: SEither Integer Bool)
-- False
-- >>> isRight (sRight sTrue :: SEither Integer Bool)
-- True
isRight :: (SymVal a, SymVal b) => SEither a b -> SBV Bool
isRight = either (const sFalse) (const sTrue)

-- | Construct an @SEither a b@ from an @Either (SBV a) (SBV b)@
--
-- >>> liftEither (Left 3 :: Either SInteger SBool)
-- Left 3 :: SEither Integer Bool
-- >>> liftEither (Right sTrue :: Either SInteger SBool)
-- Right True :: SEither Integer Bool
liftEither :: (SymVal a, SymVal b) => Either (SBV a) (SBV b) -> SEither a b
liftEither = Prelude.either sLeft sRight

-- | Case analysis for symbolic 'Either's. If the value 'isLeft', apply the
-- first function; if it 'isRight', apply the second function.
--
-- >>> either (*2) (*3) (sLeft 3)
-- 6 :: SInteger
-- >>> either (*2) (*3) (sRight 3)
-- 9 :: SInteger
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> let g = uninterpret "g" :: SInteger -> SInteger
-- >>> prove $ \x -> either f g (sLeft x) .== f x
-- Q.E.D.
-- >>> prove $ \x -> either f g (sRight x) .== g x
-- Q.E.D.
either :: forall a b c. (SymVal a, SymVal b, SymVal c)
       => (SBV a -> SBV c)
       -> (SBV b -> SBV c)
       -> SEither a b
       -> SBV c
either brA brB sab
  | Just (Left  a) <- unliteral sab
  = brA $ literal a
  | Just (Right b) <- unliteral sab
  = brB $ literal b
  | True
  = SBV $ SVal kc $ Right $ cache res
  where ka = kindOf (Proxy @a)
        kb = kindOf (Proxy @b)
        kc = kindOf (Proxy @c)

        res st = do abv <- sbvToSV st sab

                    let leftVal  = SBV $ SVal ka $ Right $ cache $ \_ -> newExpr st ka $ SBVApp (EitherAccess False) [abv]
                        rightVal = SBV $ SVal kb $ Right $ cache $ \_ -> newExpr st kb $ SBVApp (EitherAccess True)  [abv]

                        leftRes  = brA leftVal
                        rightRes = brB rightVal

                    br1 <- sbvToSV st leftRes
                    br2 <- sbvToSV st rightRes

                    --  Which branch are we in? Return the appropriate value:
                    onLeft <- newExpr st KBool $ SBVApp (EitherIs ka kb False) [abv]
                    newExpr st kc $ SBVApp Ite [onLeft, br1, br2]

-- | Map over both sides of a symbolic 'Either' at the same time
--
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> let g = uninterpret "g" :: SInteger -> SInteger
-- >>> prove $ \x -> fromLeft (bimap f g (sLeft x)) .== f x
-- Q.E.D.
-- >>> prove $ \x -> fromRight (bimap f g (sRight x)) .== g x
-- Q.E.D.
bimap :: forall a b c d.  (SymVal a, SymVal b, SymVal c, SymVal d)
      => (SBV a -> SBV b)
      -> (SBV c -> SBV d)
      -> SEither a c
      -> SEither b d
bimap brA brC = either (sLeft . brA) (sRight . brC)

-- | Map over the left side of an 'Either'
--
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> prove $ \x -> first f (sLeft x :: SEither Integer Integer) .== sLeft (f x)
-- Q.E.D.
-- >>> prove $ \x -> first f (sRight x :: SEither Integer Integer) .== sRight x
-- Q.E.D.
first :: (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b) -> SEither a c -> SEither b c
first f = bimap f id

-- | Map over the right side of an 'Either'
--
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> prove $ \x -> second f (sRight x :: SEither Integer Integer) .== sRight (f x)
-- Q.E.D.
-- >>> prove $ \x -> second f (sLeft x :: SEither Integer Integer) .== sLeft x
-- Q.E.D.
second :: (SymVal a, SymVal b, SymVal c) => (SBV b -> SBV c) -> SEither a b -> SEither a c
second = bimap id

-- | Return the value from the left component. The behavior is undefined if
-- passed a right value, i.e., it can return any value.
--
-- >>> fromLeft (sLeft (literal 'a') :: SEither Char Integer)
-- 'a' :: SChar
-- >>> prove $ \x -> fromLeft (sLeft x :: SEither Char Integer) .== (x :: SChar)
-- Q.E.D.
-- >>> sat $ \x -> x .== (fromLeft (sRight 4 :: SEither Char Integer))
-- Satisfiable. Model:
--   s0 = 'A' :: Char
--
-- Note how we get a satisfying assignment in the last case: The behavior
-- is unspecified, thus the SMT solver picks whatever satisfies the
-- constraints, if there is one.
fromLeft :: forall a b. (SymVal a, SymVal b) => SEither a b -> SBV a
fromLeft sab
  | Just (Left a) <- unliteral sab
  = literal a
  | True
  = SBV $ SVal ka $ Right $ cache res
  where ka      = kindOf (Proxy @a)
        res st = do ms <- sbvToSV st sab
                    newExpr st ka (SBVApp (EitherAccess False) [ms])

-- | Return the value from the right component. The behavior is undefined if
-- passed a left value, i.e., it can return any value.
--
-- >>> fromRight (sRight (literal 'a') :: SEither Integer Char)
-- 'a' :: SChar
-- >>> prove $ \x -> fromRight (sRight x :: SEither Char Integer) .== (x :: SInteger)
-- Q.E.D.
-- >>> sat $ \x -> x .== (fromRight (sLeft (literal 2) :: SEither Integer Char))
-- Satisfiable. Model:
--   s0 = 'A' :: Char
--
-- Note how we get a satisfying assignment in the last case: The behavior
-- is unspecified, thus the SMT solver picks whatever satisfies the
-- constraints, if there is one.
fromRight :: forall a b. (SymVal a, SymVal b) => SEither a b -> SBV b
fromRight sab
  | Just (Right b) <- unliteral sab
  = literal b
  | True
  = SBV $ SVal kb $ Right $ cache res
  where kb      = kindOf (Proxy @b)
        res st = do ms <- sbvToSV st sab
                    newExpr st kb (SBVApp (EitherAccess True) [ms])

{- HLint ignore module "Reduce duplication" -}
