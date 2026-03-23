{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Tuple2 with guard
module T where

import Data.SBV

t :: STuple Integer Integer -> SInteger
t p = [sCase| p of
               (a, b) | a .> b -> a
               (_, b)          -> b
      |]
