{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative in pCase: all constructors covered, then redundant wildcard at end
-- (sCase says "wildcard match is redundant";
--  pCase says wildcards are not allowed at all)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero      -> undefined
        Num _     -> undefined
        Var _     -> undefined
        Add _ _   -> undefined
        Let _ _ _ -> undefined
        _         -> undefined
      |]
