{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with nested tuple inside Maybe
module T where

import Data.SBV

t :: SMaybe (Integer, Bool) -> SInteger
t m = [sCase|Maybe m of
               Nothing     -> 0
               Just (a, _) -> a
      |]
