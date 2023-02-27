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

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda, lambda1, lambda2, lambda3, Expr(..)
        ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Symbolic
import Data.SBV.Provers.Prover

import qualified Data.SBV.Control.Utils as Control

import Data.SBV.Utils.PrettyNum

import Data.Proxy

-- Try:
--   lambda (\x -> x+1::SInteger)
lambda :: SymVal a => (SBV a -> SBV b) -> IO String
lambda f = do
      let cfg = defaultSMTCfg { smtLibVersion = SMTLib2 }
      let mkArg = mkSymVal (NonQueryVar (Just ALL)) Nothing
      (_, res) <- runSymbolic (Lambda cfg) $ mkArg >>= output . f

      let SMTProblem{smtLibPgm} = Control.runProofOn (Lambda cfg) QueryInternal [] res
      return $ show (smtLibPgm cfg)

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
