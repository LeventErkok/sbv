{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with Char literal patterns and wildcard
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "c" Char -> SBool))
t = calc "t" (\(Forall @"c" (c :: SChar)) -> c .== c) $ \c -> []
    |- [pCase| c of
         'a' -> c .== c =: qed
         'b' -> c .== c =: qed
         _   -> c .== c =: qed
       |]
