{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: As-pattern on tuple
module T where

import Data.SBV

t :: STuple Integer Bool -> SInteger
t p = [sCase| p of
               whole@(v, b) -> ite b v (case whole of
                                           (w, _) -> negate w)
      |]
