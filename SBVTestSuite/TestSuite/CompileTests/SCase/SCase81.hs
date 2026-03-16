{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase Bool with wildcard catch-all
module T where

import Data.SBV

t :: SBool -> SInteger
t x = [sCase| x of
               True -> 1
               _    -> 0
      |]
