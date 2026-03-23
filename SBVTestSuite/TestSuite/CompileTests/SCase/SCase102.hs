{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: As-pattern on wildcard
module T where

import Data.SBV

t :: SMaybe Integer -> SInteger
t m = [sCase| m of
               x@_ -> case x of
                         Just v  -> v
                         Nothing -> 0
      |]
