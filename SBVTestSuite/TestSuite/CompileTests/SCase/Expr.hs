{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Expr where

import Data.SBV

data Expr = Zero
          | Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr
          deriving Show

mkSymbolic [''Expr]
