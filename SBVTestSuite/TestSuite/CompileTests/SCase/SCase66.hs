{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with nested list inside Either
module T where

import Prelude hiding (null, head, tail)
import Data.SBV

t :: SEither ([] Integer) Bool -> SInteger
t e = [sCase| e of
               Left (x : _) -> x
               Left []      -> 0
               Right _      -> 1
      |]
