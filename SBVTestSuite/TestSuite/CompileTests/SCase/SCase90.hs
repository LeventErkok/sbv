{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Nested case expressions. Inner case on Maybe inside outer case on Expr.
module T where

import Expr
import Data.SBV

t :: SExpr -> SMaybe Integer -> SInteger
t e m = [sCase| e of
                Zero      -> case m of
                               Nothing -> 0
                               Just v  -> v
                Num k     -> k
                Var _     -> -1
                Add a b   -> t a m + t b m
                Let _ _ b -> t b m
       |]
