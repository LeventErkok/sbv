{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Negative: Non-exhaustive inner case (missing Nothing).
module T where

import Expr
import Data.SBV

t :: SExpr -> SMaybe Integer -> SInteger
t e m = [sCase| e of
                Zero      -> case m of
                               Just v -> v
                Num k     -> k
                Var _     -> -1
                Add a b   -> t a m + t b m
                Let _ _ b -> t b m
       |]
