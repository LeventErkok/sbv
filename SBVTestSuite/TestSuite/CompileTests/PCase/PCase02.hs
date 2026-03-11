{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Bad syntax
t :: SExpr -> Proof SBool
t e = [pCase| e + 1|]
