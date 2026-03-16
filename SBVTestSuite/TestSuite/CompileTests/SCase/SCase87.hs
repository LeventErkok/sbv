{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase String non-exhaustive (only literals, no catch-all) — should fail
module T where

import Data.SBV

t :: SString -> SInteger
t s = [sCase| s of
               "hello" -> 1
               "world" -> 2
      |]
