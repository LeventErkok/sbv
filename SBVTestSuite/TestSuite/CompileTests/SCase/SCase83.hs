{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds   #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Int16 integer literals, variable binding, and guard
module T where

import Data.SBV

t :: SInt16 -> SInt16
t x = [sCase| x of
               0          -> 0
               1          -> 100
               n | n .> 0 -> n
                 | sTrue   -> -n
      |]
