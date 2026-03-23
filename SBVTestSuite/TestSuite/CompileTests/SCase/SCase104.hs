{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: As-pattern where binding is unused (should be elided)
module T where

import Data.SBV

t :: SMaybe Integer -> SInteger
t m = [sCase| m of
               _unused@(Just v) -> v
               Nothing          -> 0
      |]
