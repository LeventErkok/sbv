{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Unknown constructor
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero  -> undefined
        Numb _ -> undefined
      |]
