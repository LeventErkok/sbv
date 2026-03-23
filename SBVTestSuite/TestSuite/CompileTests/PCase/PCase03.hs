{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Not usable in declaration context
[pCase| e of
        Zero  -> undefined
        Num _ -> undefined
      |]

{- HLint ignore module "Unused LANGUAGE pragma" -}
