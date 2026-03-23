{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with List, nested cons pattern
module T where

import Prelude hiding (null, head, tail)
import Data.SBV

t :: SList Integer -> SInteger
t xs = [sCase| xs of
                []          -> 0
                a : (b : _) -> a + b
                _ : _       -> 1
       |]
