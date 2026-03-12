{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with wildcard-only, no guards
module T where

import Data.SBV

t :: SInteger -> SInteger
t x = [sCase| x of
               _ -> x + 1
      |]
