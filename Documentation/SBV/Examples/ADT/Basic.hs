-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Basic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Basic ADT examples.
-----------------------------------------------------------------------------
{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE TemplateHaskell #-}

module Documentation.SBV.Examples.ADT.Basic where

import Data.SBV

-- | A basic arithmetic expression type
data Expr = Var String
          | Num Integer
          | Add Expr Expr
          | Let String Expr Expr

-- | Make it a symbolic value
mkSymbolicADT ''Expr

-- | Create two different values:
--
-- >>> test
-- Satisfiable. Model:
--   s0 = Add (Num 0) (Num 0) :: Expr
--   s1 =               Num 0 :: Expr
test :: IO SatResult
test = satWith z3{verbose=True} $ \x y -> x ./= (y :: SExpr) -- .&& y ./= literal (Num 0)
