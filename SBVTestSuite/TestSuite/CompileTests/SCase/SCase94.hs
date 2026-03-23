{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Nested case with wildcard in inner case.
module T where

import Expr
import Data.SBV

t :: SExpr -> SMaybe Integer -> SInteger
t e m = [sCase| e of
                Zero  -> case m of
                           Just v -> v
                           _      -> 0
                Num k     -> k
                _         -> case m of
                               Nothing -> -1
                               _       -> 42
       |]
