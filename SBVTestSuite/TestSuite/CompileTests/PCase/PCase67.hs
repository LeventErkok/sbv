{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Test: pCase with List, nested cons pattern with bindings
module T where

import Prelude hiding (null, head, tail, length)
import Data.SBV
import Data.SBV.List (length)
import Data.SBV.TP

t :: TP (Proof (Forall "xs" [Integer] -> SBool))
t = calc "t" (\(Forall @"xs" (xs :: SList Integer)) -> length xs .>= 0) $ \xs -> []
    |- [pCase| xs of
         []              -> length xs .>= 0 =: qed
         _ : (_ : _)     -> length xs .>= 0 =: qed
         _ : _           -> length xs .>= 0 =: qed
       |]
