{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with negative integer literal (uses LitP with negative value)
module T where

import Data.SBV

t :: SInteger -> SBool
t x = [sCase| x of
               0    -> sTrue
               (-1) -> sTrue
               _    -> sFalse
      |]
