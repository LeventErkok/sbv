-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Param
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- An example of parameterized ADTs
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module Documentation.SBV.Examples.ADT.Param where

import Data.SBV

-- | A basic parameterized type
data Expr a = E a
{-
data Expr nm a = Var nm
               | Val nm
               | Add    (Expr nm a) (Expr nm a)
               | Mul    (Expr nm a) (Expr nm a)
               | Let nm (Expr nm a) (Expr nm a)
-}

-- | Create a symbolic version of expressions.
mkSymbolic ''Expr
