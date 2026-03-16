{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with integer literal pattern and wildcard
module T where

import Data.SBV

t :: SInteger -> SBool
t x = [sCase| x of
               0 -> sTrue
               _ -> sFalse
      |]
