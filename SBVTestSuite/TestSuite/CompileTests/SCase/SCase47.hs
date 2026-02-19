{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: Num 1 without a fallback for the Num constructor
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero      -> 0
               Num 1     -> 100
               Var _     -> -1
               Add a b   -> t a + t b
               Let _ _ b -> t b
      |]
