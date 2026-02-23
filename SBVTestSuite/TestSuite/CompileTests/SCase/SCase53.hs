{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

-- Dump test: nested pattern with user guard (combines nesting + guard accumulation)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Add (Num i) b | i .> 0   -> i + t b
                              | i .> -5  -> t b
               Add a b                   -> t a + t b
               Zero                      -> 0
               Num i                     -> i
               Var _                     -> 1
               Let _ _ _                 -> 3
      |]
