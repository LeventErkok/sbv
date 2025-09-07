{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
        Zero  -> 0
        Num _ _ -> i
        Var _ -> 0
        Add _ _ -> 2
        Let _ _ _ -> 3
      |]
