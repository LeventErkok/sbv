{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with string literal patterns
module T where

import Data.SBV

t :: SString -> SInteger
t s = [sCase| s of
               "hello" -> 1
               "world" -> 2
               _       -> 0
      |]
