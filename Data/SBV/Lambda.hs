-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A simple expression language over closed terms, used in creating
-- lambda-expressions for (limited) higher-order function support.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda
        ) where

import Control.Monad.Trans

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.Provers.Prover
import Data.SBV.SMT.SMTLib

import Data.Proxy

-- | Extract an SMTLib compliand lambda string
-- >>> lambda (2 :: SInteger)
-- WHAT
-- >>> lambda (\x -> x+1::SInteger)
-- WHAT
-- >>> lambda (\x y -> x+y*2 :: SInteger)
-- WHAT
-- >>> lambda (\x (y, z) -> x+y*2+z :: SInteger)
-- WHAT
-- >>> lambda (\x (y, z) k -> x+y*2+z + k :: SInteger)
-- WHAT
lambda :: Lambda Symbolic a => a -> IO String
lambda f = do st  <- mkNewState Lambda
              res <- fst <$> runSymbolicInState st (mkLambda st f)
              let SMTLibPgm _ p = sh res
              pure $ unlines p
 where sh :: Result -> SMTLibPgm
       sh (Result ki _qcInfo _observables _codeSegs is consts tbls arrs uis axs pgm cstrs _assertions outputs) =
           toSMTLib defaultSMTCfg{ smtLibVersion = SMTLib2 }
                    QueryInternal
                    ki
                    True
                    []
                    is
                    []
                    consts
                    tbls
                    arrs
                    uis
                    axs
                    pgm
                    cstrs
                    (head outputs)
                    defaultSMTCfg{ smtLibVersion = SMTLib2 }

-- | Values that we can turn into a lambda abstraction
class MonadSymbolic m => Lambda m a where
  mkLambda :: State -> a -> m Result

-- | Turn a symbolic computation to an encapsulated lambda
instance MonadSymbolic m => Lambda m (SymbolicT m (SBV a)) where
  mkLambda st cmp = do ((), res) <- runSymbolicInState st (cmp >>= output >> return ())
                       pure res

-- | Base case, simple values
instance MonadSymbolic m => Lambda m (SBV a) where
  mkLambda st = mkLambda st . (pure :: SBV a -> SymbolicT m (SBV a))

-- | Functions
instance (SymVal a, Lambda m r) => Lambda m (SBV a -> r) where
  mkLambda st fn = mkLambda st =<< fn <$> mkArg
    where mkArg = do let k = kindOf (Proxy @a)
                     sv <- liftIO $ internalVariable st k
                     pure $ SBV $ SVal k (Right (cache (const (return sv))))

-- | Functions of 2-tuple argument
instance (SymVal a, SymVal b, Lambda m r) => Lambda m ((SBV a, SBV b) -> r) where
  mkLambda st fn = mkLambda st $ \a b -> fn (a, b)

-- | Functions of 3-tuple arguments
instance (SymVal a, SymVal b, SymVal c, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c) -> r) where
  mkLambda st fn = mkLambda st $ \a b c -> fn (a, b, c)

-- | Functions of 4-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d-> fn (a, b, c, d)

-- | Functions of 5-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d e -> fn (a, b, c, d, e)

-- | Functions of 6-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d e f -> fn (a, b, c, d, e, f)

-- | Functions of 7-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d e f g -> fn (a, b, c, d, e, f, g)
