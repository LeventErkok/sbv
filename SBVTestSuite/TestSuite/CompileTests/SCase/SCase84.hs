{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase Integer non-exhaustive (all guarded, no catch-all) — should fail
module T where

import Data.SBV

t :: SInteger -> SBool
t x = [sCase| x of
               0 -> sTrue
               1 -> sFalse
      |]
