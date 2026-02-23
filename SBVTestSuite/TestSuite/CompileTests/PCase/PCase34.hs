{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative in pCase: two wildcards
-- (sCase says "wildcard makes remaining matches redundant";
--  pCase says wildcards are not allowed at all)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero  -> undefined
        Num _ -> undefined
        _     -> undefined
        _     -> undefined
      |]
