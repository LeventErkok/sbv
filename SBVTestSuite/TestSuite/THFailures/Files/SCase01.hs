{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module SCase01 where

import Data.SBV

data Expr = Zero
          | Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr
          deriving Show

mkSymbolic ''Expr

t :: SExpr -> SInteger
t e = [sCase|Expr e of|]
