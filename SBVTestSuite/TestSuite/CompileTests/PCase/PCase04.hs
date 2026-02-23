{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Unknown type
t :: SExpr -> Proof SBool
t e = [pCase|FExpr e of
        Num _ -> undefined
      |]
