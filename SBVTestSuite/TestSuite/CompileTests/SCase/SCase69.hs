{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with guarded wildcards only
module T where

import Data.SBV

t :: SInteger -> SInteger
t x = [sCase| x of
               _ | x .> 0 -> x
                 | sTrue   -> -x
      |]
