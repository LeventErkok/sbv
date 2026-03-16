{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: sCase with char literal patterns
module T where

import Data.SBV

t :: SChar -> SBool
t c = [sCase| c of
               'a' -> sTrue
               'b' -> sTrue
               _   -> sFalse
      |]
