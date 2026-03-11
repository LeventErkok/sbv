{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with Maybe, nested Either pattern
module T where

import Data.SBV

t :: SMaybe (Either Integer Bool) -> SInteger
t m = [sCase|Maybe m of
               Nothing          -> 0
               Just (Left x)    -> x
               Just (Right _)   -> 1
      |]
