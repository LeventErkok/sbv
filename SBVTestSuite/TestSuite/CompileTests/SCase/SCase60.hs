{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with List and guards
module T where

import Prelude hiding (null, head, tail)
import Data.SBV

t :: SList Integer -> SInteger
t xs = [sCase| xs of
                []         -> 0
                y : _ | y .== 5 -> 100
                _ : ys     -> t ys
       |]
