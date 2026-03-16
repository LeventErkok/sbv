{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with String literal patterns and wildcard
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "s" String -> SBool))
t = calc "t" (\(Forall @"s" (s :: SString)) -> s .== s) $ \s -> []
    |- [pCase| s of
         "hello" -> s .== s =: qed
         _       -> s .== s =: qed
       |]
