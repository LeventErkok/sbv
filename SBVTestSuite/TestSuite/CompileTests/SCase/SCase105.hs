{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: As-pattern on list cons pattern
module T where

import Data.SBV

t :: SList Integer -> SInteger
t xs = [sCase| xs of
                a : tl@(_ : _) -> a + case tl of
                                         b : _ -> b
                                         []    -> 0
                _ : _           -> 0
                []              -> 0
       |]
