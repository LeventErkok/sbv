{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-name-shadowing -ddump-splices #-}

-- Positive: Scoping regression test for pCase. Pattern var 'k' from 'Num k' is
-- used in one branch of a nested case on SBool, while a sibling branch shadows
-- 'k' with a let binding. Old scope-unaware freeVars would drop the accessor
-- binding for 'k', causing a compilation error. See also SCase107 for the sCase
-- counterpart.
module T where

import Expr
import Data.SBV
import Data.SBV.TP

t :: TP (Proof (Forall "e" Expr -> Forall "b" Bool -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) (Forall @"b" (_ :: SBool)) -> e .== e) $ \e b -> []
    |- [pCase| e of
         Zero    -> e .== e =: qed
         Num k   -> case b of
                      True  -> let k = (0 :: SInteger) in k .== k =: e .== e =: qed
                      False -> k .>= 0 .|| e .== e =: sTrue =: qed
         Var _   -> e .== e =: qed
         Add _ _ -> e .== e =: qed
         Let _ _ _ -> e .== e =: qed
       |]
