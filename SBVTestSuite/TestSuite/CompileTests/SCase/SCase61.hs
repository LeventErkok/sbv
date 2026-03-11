{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with Maybe, guards on Just
module T where

import Data.SBV

t :: SMaybe Integer -> SInteger
t m = [sCase| m of
               Nothing        -> 0
               Just x | x .> 5 -> x * 2
               Just x         -> x
      |]
