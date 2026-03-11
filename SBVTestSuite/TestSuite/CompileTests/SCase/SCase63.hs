{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with Tuple3
module T where

import Data.SBV

t :: STuple3 Integer Integer Bool -> SInteger
t p = [sCase|Tuple3 p of
               (a, b, _) -> a + b
      |]
