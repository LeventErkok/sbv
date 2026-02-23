{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: overlapping — second group for same constructor after first has sTrue catch-all guard
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero             -> undefined
        Num i | i .> 3   -> undefined
              | sTrue    -> undefined
        Num i | i .> 12  -> undefined
        Var _            -> undefined
        Add _ _          -> undefined
        Let _ _ _        -> undefined
      |]
