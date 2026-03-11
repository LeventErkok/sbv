{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: sCase with List, wildcard only for cons
module T where

import Prelude hiding (null, head, tail)
import Data.SBV

t :: SList Integer -> SBool
t xs = [sCase| xs of
                []     -> sTrue
                _ : _  -> sFalse
       |]
