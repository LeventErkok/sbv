{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase Bool reversed order (False first, then True)
module T where

import Data.SBV

t :: SBool -> SInteger
t x = [sCase| x of
               False -> 0
               True  -> 1
      |]
