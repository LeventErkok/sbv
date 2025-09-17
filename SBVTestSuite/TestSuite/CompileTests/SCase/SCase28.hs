{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Num i | i > 3 -> 5
                     | sTrue -> 12

               Zero{} -> 0
               Var{}  -> 0
               Add{}  -> 0
               Let{}  -> 0
      |]
