{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with integer literal and variable binding
module T where

import Data.SBV

t :: SInteger -> SInteger
t x = [sCase| x of
               0 -> 0
               n -> n + 1
      |]
