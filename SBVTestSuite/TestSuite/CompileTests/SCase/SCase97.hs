{-# LANGUAGE QuasiQuotes  #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Negative: Inner case on ADT without mkSymbolic.
module T where

import Expr
import Data.SBV

data Color = Red | Green | Blue

t :: SExpr -> Color -> SInteger
t e c = [sCase| e of
                Zero      -> case c of
                               Red   -> 0
                               Green -> 1
                               Blue  -> 2
                Num k     -> k
                Var _     -> -1
                Add a b   -> t a c + t b c
                Let _ _ b -> t b c
       |]
