{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with integer literal and guard
module T where

import Data.SBV

t :: SInteger -> SInteger -> SInteger
t x y = [sCase| x of
                 0         -> y
                 _ | x .> y -> x
                   | sTrue  -> y
        |]
