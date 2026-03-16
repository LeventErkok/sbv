{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with Integer variable binding and guard
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "x" Integer -> SBool))
t = calc "t" (\(Forall @"x" (x :: SInteger)) -> x .== x) $ \x -> []
    |- [pCase| x of
         0         -> x .== x =: qed
         n | n .> 0 -> x .== x =: qed
           | sTrue  -> x .== x =: qed
       |]
