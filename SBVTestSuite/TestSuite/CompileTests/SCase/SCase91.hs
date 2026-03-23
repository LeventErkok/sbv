{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Same-type nesting. Inner case on Expr inside outer case on Expr.
module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase| e of
               Zero      -> 0
               Num k     -> k
               Var _     -> -1
               Add a b   -> case a of
                              Zero    -> t b
                              Num k   -> k + t b
                              Var _   -> t b
                              Add _ _ -> t a + t b
                              Let _ _ c -> t c + t b
               Let _ _ b -> t b
      |]
