{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Maybe (no guards)
module T where

import Data.SBV

t :: SMaybe Integer -> SInteger
t m = [sCase| m of
               Nothing -> 0
               Just x  -> x + 1
      |]
