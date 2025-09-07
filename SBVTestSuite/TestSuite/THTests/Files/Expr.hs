{-# LANGUAGE TemplateHaskell #-}

module Expr where

import Data.SBV

data Expr = Zero
          | Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr
          deriving Show

mkSymbolic ''Expr
