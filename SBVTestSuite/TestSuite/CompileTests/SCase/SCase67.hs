{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with Tuple2 with guard
module T where

import Data.SBV

t :: STuple Integer Integer -> SInteger
t p = [sCase|Tuple2 p of
               (a, b) | a .> b -> a
               (_, b)          -> b
      |]
