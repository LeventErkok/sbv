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

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda, lambda1, lambda2, lambda3, Expr(..)
        ) where

import Control.Monad.IO.Class

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Symbolic
import Data.SBV.Provers.Prover

import qualified Data.SBV.Control.Utils as Control

import Data.SBV.Utils.PrettyNum

import Data.Proxy

-- | Values that we can turn into a lambda abstraction
-- Try:
--   lambda (2 :: SInteger)
--   lambda (\x -> x+1::SInteger)
--   lambda (\x y -> x+y*2 :: SInteger)

class Lambda a where
  lambda :: a -> IO String

-- | Turn a symbolic computation as a lambda abstraction
generateLambda :: MonadIO m => SymbolicT m a -> m String
generateLambda x = do
   let cfg = defaultSMTCfg { smtLibVersion = SMTLib2 }

   (_, res) <- runSymbolic (Lambda cfg) x

   let SMTProblem{smtLibPgm} = Control.runProofOn (Lambda cfg) QueryInternal [] res

   liftIO $ putStrLn $ show (smtLibPgm cfg)
   pure ""

-- | All SBV values are automatically lambda's, i.e., no argument function. This
-- is also the base case for all lambda-convertible functions.
instance Lambda (SBV a) where
  lambda = generateLambda . output

-- | Functions of one argument
instance SymVal a => Lambda (SBV a -> SBV b) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of two arguments
instance (SymVal a, SymVal b) => Lambda (SBV a -> SBV b -> SBV c) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of three arguments
instance (SymVal a, SymVal b, SymVal c) => Lambda (SBV a -> SBV b -> SBV c -> SBV d) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of four arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d) => Lambda (SBV a -> SBV b -> SBV c -> SBV d -> SBV e) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of five arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e) => Lambda (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of six arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f) => Lambda (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of seven arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g) => Lambda (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g -> SBV h) where
  lambda fn = generateLambda $ output =<< fn <$> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing
                                             <*> mkSymVal (NonQueryVar (Just ALL)) Nothing

-- | Functions of 2-tuple argument
instance (SymVal a, SymVal b) => Lambda ((SBV a, SBV b) -> SBV c) where
  lambda fn = lambda $ \a b -> fn (a, b)

-- | Functions of 3-tuple arguments
instance (SymVal a, SymVal b, SymVal c) => Lambda ((SBV a, SBV b, SBV c) -> SBV d) where
  lambda fn = lambda $ \a b c -> fn (a, b, c)

-- | Functions of 4-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d) => Lambda ((SBV a, SBV b, SBV c, SBV d) -> SBV e) where
  lambda fn = lambda $ \a b c d-> fn (a, b, c, d)

-- | Functions of 5-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e) => Lambda ((SBV a, SBV b, SBV c, SBV d, SBV e) -> SBV f) where
  lambda fn = lambda $ \a b c d e -> fn (a, b, c, d, e)

-- | Functions of 6-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f) => Lambda ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> SBV g) where
  lambda fn = lambda $ \a b c d e f -> fn (a, b, c, d, e, f)

-- | Functions of 7-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g) => Lambda ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> SBV h) where
  lambda fn = lambda $ \a b c d e f g -> fn (a, b, c, d, e, f, g)

-- | This module doesn't implement everything yet.
tbd :: String -> a
tbd s = error $ "Data.SBV.Lamda: TBD: " ++ s

-- | Type of expressions, with a phantom parameter to keep track of source-level typing.
newtype Expr a = Expr { getExpr :: String }

-- | Lift an operation over various kinds.
lift2 :: HasKind t => t -> String -> String -> [String] -> Expr a
lift2 t intOp bvOp args = case kindOf t of
                            KUnbounded -> mk intOp
                            KBounded{} -> mk bvOp
                            k          -> tbd $ "lif2 on kind: " ++ show k
  where mk op = Expr $ "(" ++ op ++ " " ++ unwords args ++ ")"

-- | 'Num' instance for 'Expr'.
instance (SymVal a, Ord a, Num a) => Num (Expr a) where
  fromInteger i   = Expr $ cvToSMTLib RoundNearestTiesToEven (mkConstCV (kindOf (Proxy @a)) i)
  Expr a + Expr b = lift2 (Proxy @a) "+" "bvadd" [a, b]
  Expr a - Expr b = lift2 (Proxy @a) "-" "bvsub" [a, b]
  Expr a * Expr b = lift2 (Proxy @a) "*" "bvmul" [a, b]
  abs    _        = tbd "abs on Num (Expr a)"
  signum _        = tbd "signum on Num (Expr a)"

-- | Create a lambda expression
mkLambda :: [String] -> Expr a -> String
mkLambda decls body = "(lambda (" ++ unwords decls ++ ") " ++ getExpr body ++ ")"

-- | Make sure this variable is uniquely tagged
internalTag :: String -> String
internalTag = ("__internal_sbv_" ++)

-- | Make a variable declaration
decl :: HasKind a => String -> a -> String
decl n t = "(" ++ internalTag n ++ " " ++ smtType (kindOf t) ++ ")"

-- | Make the variable into an expression, by tagging it
mkExpr :: String -> Expr a
mkExpr = Expr . internalTag

-- | Create a single argument lambda-function
lambda1 :: forall a b. HasKind a => String -> (Expr a -> Expr b) -> String
lambda1 nm f = mkLambda [decl nm (Proxy @a)] (f (mkExpr nm))

-- | Create a two argument lambda-function
lambda2 :: forall a b c. (HasKind a, HasKind b) => String -> String -> (Expr a -> Expr b -> Expr c) -> String
lambda2 nm1 nm2 f = mkLambda [decl nm1 (Proxy @a), decl nm2 (Proxy @b)] (f (mkExpr nm1) (mkExpr nm2))

-- | Create a three argument lambda-function
lambda3 :: forall a b c d. (HasKind a, HasKind b, HasKind c) => String -> String -> String -> (Expr a -> Expr b -> Expr c -> Expr d) -> String
lambda3 nm1 nm2 nm3 f = mkLambda [decl nm1 (Proxy @a), decl nm2 (Proxy @b), decl nm3 (Proxy @c)] (f (mkExpr nm1) (mkExpr nm2) (mkExpr nm3))
