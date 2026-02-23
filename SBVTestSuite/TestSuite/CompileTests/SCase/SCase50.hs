{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

-- Dump test: multiple guards on same constructor (guard accumulation, ite chain)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero              -> 0
               Num i | i .< 3    -> i
                     | i .< 10   -> i + 1
               Num i             -> i + 2
               Var _             -> 1
               Add _ _           -> 2
               Let _ _ _         -> 3
      |]
