{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with multiple integer literals and wildcard
module T where

import Data.SBV

t :: SInteger -> SInteger
t x = [sCase| x of
               0 -> 10
               1 -> 20
               2 -> 30
               _ -> x
      |]
