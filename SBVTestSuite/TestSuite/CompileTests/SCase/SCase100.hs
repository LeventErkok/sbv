{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Top-level as-pattern on Maybe
module T where

import Data.SBV

t :: SMaybe Integer -> SInteger
t m = [sCase| m of
               whole@(Just v) -> v + case whole of
                                       Just w  -> w
                                       Nothing -> 0
               Nothing        -> 0
      |]
