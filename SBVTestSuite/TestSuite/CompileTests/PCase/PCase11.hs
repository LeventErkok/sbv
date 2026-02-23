{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Unknown constructor in nested pattern
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero           -> undefined
        Num k          -> undefined
        Var _          -> undefined
        Add (Numb i) b -> undefined
        Let _ _ _      -> undefined
      |]
