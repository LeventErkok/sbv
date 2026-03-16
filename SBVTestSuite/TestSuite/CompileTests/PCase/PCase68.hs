{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with Bool constructor patterns
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "b" Bool -> SBool))
t = calc "t" (\(Forall @"b" (b :: SBool)) -> b .== b) $ \b -> []
    |- [pCase| b of
         True  -> b .== b =: qed
         False -> b .== b =: qed
       |]
