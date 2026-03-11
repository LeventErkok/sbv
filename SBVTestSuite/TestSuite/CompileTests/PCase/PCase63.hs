{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- Test: pCase with List
module T where

import Prelude hiding (null, head, tail)
import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "xs" [Integer] -> SBool))
t = calc "t" (\(Forall @"xs" (xs :: SList Integer)) -> xs .== xs) $ \xs -> []
    |- [pCase| xs of
         []    -> xs .== xs =: qed
         _ : _ -> xs .== xs =: qed
       |]
