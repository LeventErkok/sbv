{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: nested pattern using parenthesized constructor (ParensP)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero                    -> 0
               Num k                   -> k
               Var s                   -> ite (s .== literal "a") 1 2
               Let _ (Num i) b         -> i + t b
               Let _ a       b         -> t a + t b
               Add a b                 -> t a + t b
      |]
