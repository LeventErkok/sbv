{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase Bool non-exhaustive (only True, no wildcard) — should fail
module T where

import Data.SBV

t :: SBool -> SInteger
t x = [sCase| x of
               True -> 1
      |]
