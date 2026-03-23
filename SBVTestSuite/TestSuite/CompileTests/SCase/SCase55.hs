{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Either (no guards)
module T where

import Data.SBV

t :: SEither Integer Bool -> SInteger
t e = [sCase| e of
               Left a  -> a
               Right _ -> 0
      |]
