{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: pCase with Either
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "e" (Either Integer Bool) -> SBool))
t = calc "t" (\(Forall @"e" (e :: SEither Integer Bool)) -> e .== e) $ \e -> []
    |- [pCase|Either e of
         Left _  -> e .== e =: qed
         Right _ -> e .== e =: qed
       |]
