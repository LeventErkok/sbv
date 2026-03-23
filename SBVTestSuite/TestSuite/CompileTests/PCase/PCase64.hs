{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with Tuple2
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "p" (Integer, Bool) -> SBool))
t = calc "t" (\(Forall @"p" (p :: STuple Integer Bool)) -> p .== p) $ \p -> []
    |- [pCase| p of
         (_, _) -> p .== p =: qed
       |]
