{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with integer literal patterns (no dump, just compilation check)
-- Tests that the generated code actually type-checks with SBV types
module T where

import Data.SBV

clamp :: SInteger -> SInteger
clamp x = [sCase| x of
                   0 -> 0
                   1 -> 1
                   n -> ite (n .> 0) 100 (-100)
           |]
