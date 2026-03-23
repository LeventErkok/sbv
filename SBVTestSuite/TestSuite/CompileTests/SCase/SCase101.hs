{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Nested as-pattern on Either inside Maybe
module T where

import Data.SBV

t :: SMaybe (Either Integer Bool) -> SInteger
t m = [sCase| m of
               Just inner@(Left v)  -> v + case inner of
                                              Left w  -> w
                                              Right _ -> 0
               Just (Right _)       -> 1
               Nothing              -> 0
      |]
