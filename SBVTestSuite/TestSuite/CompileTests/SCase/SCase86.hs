{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds   #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Word8 and mixed literal/variable/wildcard
module T where

import Data.SBV

t :: SWord8 -> SWord8 -> SWord8
t x y = [sCase| x of
                 0         -> y
                 n | n .> y -> n
                   | sTrue  -> y
        |]
