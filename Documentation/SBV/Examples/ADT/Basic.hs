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
{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

{-# LANGUAGE TemplateHaskell #-}

module Documentation.SBV.Examples.ADT.Basic where

import Data.SBV

-- | A basic arithmetic expression type
data Expr = Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr

mkSymbolic ''Expr

-- | Create two different values:
--
-- >>> test
test :: IO SatResult
test = satWith z3{verbose=True} $ \x y -> x ./== (y :: SExpr) .&& y .== literal (Let "x" (Num 12) (Add (Var "x") (Num 3)))
