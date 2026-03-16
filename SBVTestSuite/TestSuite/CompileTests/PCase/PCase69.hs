{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with Bool, guard on True
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "b" Bool -> Forall "x" Integer -> SBool))
t = calc "t" (\(Forall @"b" (b :: SBool)) (Forall @"x" (x :: SInteger)) -> b .|| sNot b) $ \b x -> []
    |- [pCase| b of
         True  | x .> 0 -> b .|| sNot b =: qed
               | sTrue  -> b .|| sNot b =: qed
         False           -> b .|| sNot b =: qed
       |]
