{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: pCase with Maybe, guards on Just
module T where

import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "m" (Maybe Integer) -> SBool))
t = calc "t" (\(Forall @"m" (m :: SMaybe Integer)) -> m .== m) $ \m -> []
    |- [pCase|Maybe m of
         Nothing          -> m .== m =: qed
         Just x | x .> 0  -> m .== m =: qed
                | sTrue    -> m .== m =: qed
       |]
