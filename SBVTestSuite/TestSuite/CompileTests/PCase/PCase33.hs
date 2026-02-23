{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative in pCase: wildcard mid-list (after two constructors, before more)
-- (sCase says "wildcard makes remaining matches redundant";
--  pCase says wildcards are not allowed at all)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero  -> undefined
        Num _ -> undefined
        _     -> undefined
        Var _ -> undefined
        Add _ _ -> undefined
        Let _ _ _ -> undefined
      |]
