{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Either, guards and wildcard
module T where

import Data.SBV

t :: SEither Integer Integer -> SInteger
t e = [sCase| e of
               Left x | x .> 0 -> x
               _               -> 0
      |]
