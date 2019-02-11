-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Either
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic sums, similar to Haskell's 'Either' type.
-----------------------------------------------------------------------------

{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.SBV.Either (
    -- * Constructing sums
    sLeft, sRight, liftEither
    -- * Destructing sums
    , either
    -- * Mapping functions
    , bimap, first, second
    -- * Scrutinizing branches of a sum
    , isLeft, isRight
  ) where

import           Prelude hiding (either)
import qualified Prelude

import Data.Proxy (Proxy(Proxy))

import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

-- | Construct an @SEither a b@ from an @SBV a@
sLeft :: forall a b. (SymVal a, SymVal b) => SBV a -> SEither a b
sLeft sa
  | Just a <- unliteral sa
  = literal (Left a)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Either a b))
        res st = do asv <- sbvToSV st sa
                    newExpr st k $ SBVApp (EitherConstructor False) [asv]

-- | Construct an @SEither a b@ from an @SBV b@
sRight :: forall a b. (SymVal a, SymVal b) => SBV b -> SEither a b
sRight sb
  | Just b <- unliteral sb
  = literal (Right b)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Either a b))
        res st = do bsv <- sbvToSV st sb
                    newExpr st k $ SBVApp (EitherConstructor True) [bsv]

-- | Construct an @SEither a b@ from an @Either a b@
liftEither :: (SymVal a, SymVal b) => Either (SBV a) (SBV b) -> SEither a b
liftEither = Prelude.either sLeft sRight

-- | Case analysis for symbolic 'Either's. If the value 'isLeft', apply the
-- first function; if it 'isRight', apply the second function.
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
                    onLeft <- newExpr st KBool $ SBVApp (EitherIs False) [abv]
                    newExpr st kc $ SBVApp Ite [onLeft, br1, br2]

-- | Map over both sides of a symbolic 'Either' at the same time
bimap :: forall a b c d.  (SymVal a, SymVal b, SymVal c, SymVal d)
      => (SBV a -> SBV b)
      -> (SBV c -> SBV d)
      -> SEither a c
      -> SEither b d
bimap brA brC = either (sLeft . brA) (sRight . brC)

-- | Map over the left side of an 'Either'
first :: (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b) -> SEither a c -> SEither b c
first f = bimap f id

-- | Map over the right side of an 'Either'
second :: (SymVal a, SymVal b, SymVal c) => (SBV b -> SBV c) -> SEither a b -> SEither a c
second = bimap id

-- | Return 'sTrue' if the given symbolic value is 'Left', 'sFalse' otherwise
isLeft :: (SymVal a, SymVal b) => SEither a b -> SBV Bool
isLeft = either (const sTrue) (const sFalse)

-- | Return 'sTrue' if the given symbolic value is 'Right', 'sFalse' otherwise
isRight :: (SymVal a, SymVal b) => SEither a b -> SBV Bool
isRight = either (const sFalse) (const sTrue)
