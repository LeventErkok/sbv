{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with Bool non-exhaustive (only True)
-- (sCase would reject as non-exhaustive; pCase is fine)
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "b" Bool -> SBool))
t = calc "t" (\(Forall @"b" (b :: SBool)) -> b .== b) $ \b -> []
    |- [pCase| b of
         True -> b .== b =: qed
       |]
