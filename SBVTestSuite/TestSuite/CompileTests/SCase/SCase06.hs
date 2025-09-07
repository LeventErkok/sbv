{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- bad type
t :: SExpr -> SInteger
t e = [sCase|FExpr e of Num _ -> 1|]
