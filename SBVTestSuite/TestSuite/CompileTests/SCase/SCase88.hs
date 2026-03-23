{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase Char non-exhaustive (only literals, no catch-all) — should fail
module T where

import Data.SBV

t :: SChar -> SBool
t c = [sCase| c of
               'x' -> sTrue
               'y' -> sFalse
      |]
