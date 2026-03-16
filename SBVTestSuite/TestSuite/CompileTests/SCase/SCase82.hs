{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds   #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with Word8 integer literal patterns
module T where

import Data.SBV

t :: SWord8 -> SWord8
t x = [sCase| x of
               0 -> 10
               1 -> 20
               _ -> x
      |]
