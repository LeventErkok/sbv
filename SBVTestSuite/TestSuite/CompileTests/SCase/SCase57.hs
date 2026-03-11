{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with Tuple2
module T where

import Data.SBV

t :: STuple Integer Bool -> SInteger
t p = [sCase|Tuple2 p of
               (a, _) -> a + 1
      |]
