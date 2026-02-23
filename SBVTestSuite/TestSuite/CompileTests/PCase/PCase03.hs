{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Not usable in declaration context
[pCase|Expr e of
        Zero  -> undefined
        Num _ -> undefined
      |]

{- HLint ignore module "Unused LANGUAGE pragma" -}
