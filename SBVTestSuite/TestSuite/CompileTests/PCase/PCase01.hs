{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Parse error: EOF
t :: SExpr -> Proof SBool
t _e = [pCase|Expr _e of|]
