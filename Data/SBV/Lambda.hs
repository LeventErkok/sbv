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

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.Provers.Prover

import qualified Data.SBV.Control.Utils as Control

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
lambda f = fst <$> runSymbolic (Lambda cfg) (mkLambda f)
  where cfg = defaultSMTCfg { smtLibVersion = SMTLib2 }

-- | Values that we can turn into a lambda abstraction
class MonadSymbolic m => Lambda m a where
  mkLambda :: a -> m String

-- | Turn a symbolic computation to an encapsulated lambda
instance MonadSymbolic m => Lambda m (SymbolicT m (SBV a)) where
  mkLambda cmp = do let cfg = defaultSMTCfg { smtLibVersion = SMTLib2 }
                    (val, res) <- runSymbolic (Lambda cfg) cmp

                    let SMTProblem{smtLibPgm} = Control.runProofOn (Lambda cfg) QueryInternal [] res

                    pure $ show (smtLibPgm cfg) ++ "\n" ++ show val

-- | Base case, simple values
instance MonadSymbolic m => Lambda m (SBV a) where
  mkLambda = mkLambda . (output :: SBV a -> SymbolicT m (SBV a))

-- | Functions
instance (SymVal a, Lambda m r) => Lambda m (SBV a -> r) where
  mkLambda fn = mkLambda =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of 2-tuple argument
instance (SymVal a, SymVal b, Lambda m r) => Lambda m ((SBV a, SBV b) -> r) where
  mkLambda fn = mkLambda $ \a b -> fn (a, b)

-- | Functions of 3-tuple arguments
instance (SymVal a, SymVal b, SymVal c, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c) -> r) where
  mkLambda fn = mkLambda $ \a b c -> fn (a, b, c)

-- | Functions of 4-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d) -> r) where
  mkLambda fn = mkLambda $ \a b c d-> fn (a, b, c, d)

-- | Functions of 5-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> r) where
  mkLambda fn = mkLambda $ \a b c d e -> fn (a, b, c, d, e)

-- | Functions of 6-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> r) where
  mkLambda fn = mkLambda $ \a b c d e f -> fn (a, b, c, d, e, f)

-- | Functions of 7-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r) where
  mkLambda fn = mkLambda $ \a b c d e f g -> fn (a, b, c, d, e, f, g)
