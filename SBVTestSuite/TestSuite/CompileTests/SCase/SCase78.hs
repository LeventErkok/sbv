{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Bool constructor patterns
module T where

import Data.SBV

t :: SBool -> SBool
t x = [sCase| x of
               True  -> sTrue
               False -> sFalse
      |]
