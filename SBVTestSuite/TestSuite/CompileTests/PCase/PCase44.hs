{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: wildcard catch-all after multi-arm guarded Var and Num
-- (sCase accepts this; pCase rejects the wildcard)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Var s | s .== literal "a"                       -> undefined
              | s .== literal "b" .|| s .== literal "c" -> undefined
              | sTrue                                    -> undefined

        Num _ | sTrue                                    -> undefined

        _                                                -> undefined
      |]
