{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Bool patterns and guard
module T where

import Data.SBV

t :: SBool -> SInteger -> SInteger
t b x = [sCase| b of
                 True  | x .> 0 -> x
                 True           -> 0
                 False          -> -x
        |]
