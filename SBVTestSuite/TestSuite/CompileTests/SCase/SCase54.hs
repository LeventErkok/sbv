{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with Maybe (no guards)
module T where

import Data.SBV

t :: SMaybe Integer -> SInteger
t m = [sCase|Maybe m of
               Nothing -> 0
               Just x  -> x + 1
      |]
