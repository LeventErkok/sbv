-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.EUFLogic
-- License   : BSD3
-- Stability : experimental
--
-- Demonstrates the ability to generate uninterpreted functions of arbitrarily
-- many arguments, whose types are generated programmatically. The high-level
-- idea of this module is to provide a strongly-typed representation, using a
-- GADT, of a logic that includes uninterpreted functions. This module then
-- defines an interpretation of this logic into SBV, which it uses to perform
-- SMT queries in the logic.
-----------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}


module Documentation.SBV.Examples.Uninterpreted.EUFLogic where

import GHC.TypeLits
import Data.Kind
import Data.Type.Equality
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import Data.SBV


----------------------------------------------------------------------
-- * Types of the EUF Logic
----------------------------------------------------------------------

-- | The datakind for the types in our EUF logic
data EUFType = Tp_Bool | Tp_BV Natural

-- | A singleton type for natural numbers that can be used as the widths of
-- bitvectors
data BVWidth w =
  (KnownNat w, BVIsNonZero w) => BVWidth (SNat w)

-- | Create a 'BVWidth' object for a 'KnownNat' that is non-zero
knownBVWidth :: (KnownNat w, BVIsNonZero w) => BVWidth w
knownBVWidth = BVWidth natSing

instance TestEquality BVWidth where
  testEquality (BVWidth w1) (BVWidth w2)
    | Just Refl <- testEquality w1 w2
    = Just Refl
  testEquality _ _ = Nothing

-- | A singleton type that represents type-level 'EUFType's at the object level
data TypeRepr (tp :: EUFType) where
  Repr_Bool :: TypeRepr Tp_Bool
  Repr_BV :: BVWidth w -> TypeRepr (Tp_BV w)

instance TestEquality TypeRepr where
  testEquality Repr_Bool Repr_Bool = Just Refl
  testEquality (Repr_BV w1) (Repr_BV w2)
    | Just Refl <- testEquality w1 w2
    = Just Refl
  testEquality _ _ = Nothing

-- | A list of 'TypeRepr's for each type in a type-level list
data TypeReprs tps where
  Repr_Nil :: TypeReprs '[]
  Repr_Cons :: TypeRepr tp -> TypeReprs tps -> TypeReprs (tp ': tps)

instance TestEquality TypeReprs where
  testEquality Repr_Nil Repr_Nil = Just Refl
  testEquality (Repr_Cons tps1 tp1) (Repr_Cons tps2 tp2)
    | Just Refl <- testEquality tps1 tps2
    , Just Refl <- testEquality tp1 tp2
    = Just Refl
  testEquality _ _ = Nothing

-- | An 'EUFType' with a known 'TypeRepr' representation
class KnownEUFType tp where
  knownEUFType :: TypeRepr tp

instance KnownEUFType Tp_Bool where
  knownEUFType = Repr_Bool

instance (KnownNat w, BVIsNonZero w) => KnownEUFType (Tp_BV w) where
  knownEUFType = Repr_BV (BVWidth natSing)

-- | A sequence of 'EUFTypes' with a known 'TypeReprs' representation
class KnownEUFTypes tps where
  knownEUFTypes :: TypeReprs tps

instance KnownEUFTypes '[] where
  knownEUFTypes = Repr_Nil

instance (KnownEUFType tp, KnownEUFTypes tps) => KnownEUFTypes (tp ': tps) where
  knownEUFTypes = Repr_Cons knownEUFType knownEUFTypes


----------------------------------------------------------------------
-- * Operations of the EUF Logic
----------------------------------------------------------------------

-- | An uninterpreted function in our EUF logic, which is a string name plus
-- the input and output types
data UnintOp (ins :: [EUFType]) (out :: EUFType) =
  UnintOp { unintOpName :: String,
            unintOpIns :: TypeReprs ins,
            unintOpOut :: TypeRepr out }

-- | The operations of our EUF logic, which are indexed by a list of 0 or more
-- input types and a single output type
data Op (ins :: [EUFType]) (out :: EUFType) where
  -- Uninterpreted functions
  Op_Unint :: UnintOp ins out -> Op ins out

  -- Boolean operations
  Op_And :: Op (Tp_Bool ': Tp_Bool ': '[]) Tp_Bool
  Op_Or :: Op (Tp_Bool ': Tp_Bool ': '[]) Tp_Bool
  Op_Not :: Op (Tp_Bool ': '[]) Tp_Bool
  Op_BoolLit :: Bool -> Op '[] Tp_Bool
  Op_IfThenElse :: TypeRepr a -> Op (Tp_Bool ': a ': a ': '[]) a

  -- Bitvector operations
  Op_Plus :: BVWidth w -> Op (Tp_BV w ': Tp_BV w ': '[]) (Tp_BV w)
  Op_Minus :: BVWidth w -> Op (Tp_BV w ': Tp_BV w ': '[]) (Tp_BV w)
  Op_Times :: BVWidth w -> Op (Tp_BV w ': Tp_BV w ': '[]) (Tp_BV w)
  Op_Abs :: BVWidth w -> Op (Tp_BV w ': '[]) (Tp_BV w)
  Op_Signum :: BVWidth w -> Op (Tp_BV w ': '[]) (Tp_BV w)
  Op_BVLit :: BVWidth w -> Integer -> Op '[] (Tp_BV w)
  Op_BVEq :: BVWidth w -> Op (Tp_BV w ': Tp_BV w ': '[]) Tp_Bool
  Op_BVLt :: BVWidth w -> Op (Tp_BV w ': Tp_BV w ': '[]) Tp_Bool

-- | Create an uninterpreted 'Op' of known type
mkUnintOp :: (KnownEUFTypes ins, KnownEUFType out) => String -> Op ins out
mkUnintOp nm = Op_Unint $ UnintOp nm knownEUFTypes knownEUFType

-- | Get the input types and output type of an 'Op'
opInsOut :: Op ins out -> (TypeReprs ins, TypeRepr out)
opInsOut (Op_Unint uop) = (unintOpIns uop, unintOpOut uop)
opInsOut Op_And = (knownEUFTypes, knownEUFType)
opInsOut Op_Or = (knownEUFTypes, knownEUFType)
opInsOut Op_Not = (knownEUFTypes, knownEUFType)
opInsOut (Op_BoolLit _) = (knownEUFTypes, knownEUFType)
opInsOut (Op_IfThenElse Repr_Bool) = (knownEUFTypes, knownEUFType)
opInsOut (Op_IfThenElse (Repr_BV (BVWidth _))) = (knownEUFTypes, knownEUFType)
opInsOut (Op_Plus (BVWidth _)) = (knownEUFTypes, knownEUFType)
opInsOut (Op_Minus (BVWidth _)) = (knownEUFTypes, knownEUFType)
opInsOut (Op_Times (BVWidth _)) = (knownEUFTypes, knownEUFType)
opInsOut (Op_Abs (BVWidth _)) = (knownEUFTypes, knownEUFType)
opInsOut (Op_Signum (BVWidth _)) = (knownEUFTypes, knownEUFType)
opInsOut (Op_BVLit (BVWidth _) _) = (knownEUFTypes, knownEUFType)
opInsOut (Op_BVEq (BVWidth _)) = (knownEUFTypes, knownEUFType)
opInsOut (Op_BVLt (BVWidth _)) = (knownEUFTypes, knownEUFType)

-- | Get the input types of an 'Op'
opIns :: Op ins out -> TypeReprs ins
opIns = fst . opInsOut


----------------------------------------------------------------------
-- * Expressions of the EUF Logic
----------------------------------------------------------------------

-- | The expressions of our EUF logic, which are just operations applied to
-- argument expressions
data EUFExpr tp where
  EUFExpr :: Op ins out -> EUFExprs ins -> EUFExpr out

-- | A sequence of expressions for each type in a type-level list
data EUFExprs tps where
  EUFExprsNil :: EUFExprs '[]
  EUFExprsCons :: EUFExpr tp -> EUFExprs tps -> EUFExprs (tp ': tps)

-- | Build the type @'EUFExpr' in1 -> ... -> 'EUFExpr' inn -> out@
type family EUFExprFun (ins :: [EUFType]) (out :: EUFType) :: Type where
  EUFExprFun '[] out = EUFExpr out
  EUFExprFun (tp ': tps) out = EUFExpr tp -> EUFExprFun tps out

-- | Build an 'EUFExprFun' from a function on 'EUFExprs'
lambdaEUFExprFun :: TypeReprs ins -> (EUFExprs ins -> EUFExpr out) ->
                    EUFExprFun ins out
lambdaEUFExprFun Repr_Nil f = f EUFExprsNil
lambdaEUFExprFun (Repr_Cons _ tps) f =
  \e -> lambdaEUFExprFun tps (f . EUFExprsCons e)

-- | Apply an 'Op' to 'EUFExprs' for its input types, returning an 'EUFExpr' for
-- its output type
applyOp :: Op ins out -> EUFExprFun ins out
applyOp op = lambdaEUFExprFun (opIns op) (EUFExpr op)

instance (KnownNat w, BVIsNonZero w) => Num (EUFExpr (Tp_BV w)) where
  e1 + e2 = applyOp (Op_Plus knownBVWidth) e1 e2
  e1 - e2 = applyOp (Op_Minus knownBVWidth) e1 e2
  e1 * e2 = applyOp (Op_Times knownBVWidth) e1 e2
  abs e = applyOp (Op_Abs knownBVWidth) e
  signum e = applyOp (Op_Signum knownBVWidth) e
  fromInteger i = applyOp (Op_BVLit knownBVWidth i)

-- | Build an expression from an uninterpreted operation of a known type
mkUnintExpr :: KnownEUFType tp => String -> EUFExpr tp
mkUnintExpr nm = EUFExpr (mkUnintOp nm) EUFExprsNil


----------------------------------------------------------------------
-- * Interpreting the EUF Logic into SBV
----------------------------------------------------------------------

-- | Convert an 'EUFType' to a type of SBV expressions
type family Type2SBV (tp :: EUFType) :: Type where
  Type2SBV Tp_Bool = SBool
  Type2SBV (Tp_BV w) = SBV (WordN w)

-- | Convert the type inputs plus output of an 'Op' to a function over 'SBV'
-- values
type family OpTypes2SBV (ins :: [EUFType]) (out :: EUFType) :: Type where
  OpTypes2SBV '[] out = Type2SBV out
  OpTypes2SBV (tp ': tps) out = Type2SBV tp -> OpTypes2SBV tps out

-- | Create an 'SMTDefinable' instance for the type returned by 'OpTypes2SBV'
-- and pass it to a local function
withSMTDefOpTypes :: TypeReprs ins -> TypeRepr out ->
                     (SMTDefinable (OpTypes2SBV ins out) => a) -> a
withSMTDefOpTypes Repr_Nil Repr_Bool f = f
withSMTDefOpTypes Repr_Nil (Repr_BV (BVWidth _)) f = f
withSMTDefOpTypes (Repr_Cons Repr_Bool ins) out f =
  withSMTDefOpTypes ins out f
withSMTDefOpTypes (Repr_Cons (Repr_BV (BVWidth _)) ins) out f =
  withSMTDefOpTypes ins out f

-- | An uninterpreted function that has been resolved to an 'SBV' function
data ResolvedUnintOp =
  forall ins out. ResolvedUnintOp (UnintOp ins out) (OpTypes2SBV ins out)

-- | A 'Map' for resolving uninterpreted operations
type UnintMap = Map String ResolvedUnintOp

-- | Look up the uninterpreted op associated with a 'String' in an 'UnintMap' at
-- a particular type, raising an error if that 'String' is associated with a
-- different type. If the 'String' is not associated with any uninterpreted
-- function, create one and return it, updating the 'UnintMap'.
unintEnsure :: UnintOp ins out -> UnintMap -> (OpTypes2SBV ins out, UnintMap)
unintEnsure uop m
  | Just (ResolvedUnintOp uop' f) <- Map.lookup (unintOpName uop) m
  , Just Refl <- testEquality (unintOpIns uop) (unintOpIns uop')
  , Just Refl <- testEquality (unintOpOut uop) (unintOpOut uop')
  = (f, m)
unintEnsure uop m
  | Just _ <- Map.lookup (unintOpName uop) m
  = error ("unintEnsure: uninterpreted op " ++ unintOpName uop ++
           " used at incorrect type")
unintEnsure uop m =
  withSMTDefOpTypes (unintOpIns uop) (unintOpOut uop) $
  let f = uninterpret (unintOpName uop) in
    (f, Map.insert (unintOpName uop) (ResolvedUnintOp uop f) m)

-- | The monad for interpreting 'EUFExpr's into SBV, which is just a state monad
-- over an 'UnintMap'
type InterpM = State UnintMap

-- | Run an 'InterpM' computation starting with the empty 'UnintMap'
runInterpM :: InterpM a -> a
runInterpM = flip evalState Map.empty

-- | Interpret an 'Op' into a function over SBV values
interpOp :: Op ins out -> InterpM (OpTypes2SBV ins out)
interpOp (Op_Unint uop) = state (unintEnsure uop)
interpOp Op_And = return (.&&)
interpOp Op_Or = return (.||)
interpOp Op_Not = return sNot
interpOp (Op_BoolLit b) = return $ fromBool b
interpOp (Op_IfThenElse Repr_Bool) = return ite
interpOp (Op_IfThenElse (Repr_BV (BVWidth _))) = return ite
interpOp (Op_Plus (BVWidth _)) = return (+)
interpOp (Op_Minus (BVWidth _)) = return (-)
interpOp (Op_Times (BVWidth _)) = return (*)
interpOp (Op_Abs (BVWidth _)) = return abs
interpOp (Op_Signum (BVWidth _)) = return signum
interpOp (Op_BVLit (BVWidth _) i) = return $ fromInteger i
interpOp (Op_BVEq (BVWidth _)) = return (.==)
interpOp (Op_BVLt (BVWidth _)) = return (.<)

-- | Interpret an 'EUFExpr' into an SBV value
interpEUFExpr :: EUFExpr tp -> InterpM (Type2SBV tp)
interpEUFExpr (EUFExpr op args) =
  do f <- interpOp op
     interpApplyEUFExprs op f args

-- | Apply an interpretation of an operator to the interpretations of a sequence
-- of arguments for it
interpApplyEUFExprs :: ghost out -> OpTypes2SBV ins out -> EUFExprs ins ->
                       InterpM (Type2SBV out)
interpApplyEUFExprs _ f EUFExprsNil = return f
interpApplyEUFExprs out f (EUFExprsCons e es) =
  do f_app <- f <$> interpEUFExpr e
     interpApplyEUFExprs out f_app es

-- | Top-level call to interpret an 'EUFExpr' to an 'SBV' value
interpEUF :: EUFExpr a -> Type2SBV a
interpEUF = runInterpM . interpEUFExpr


----------------------------------------------------------------------
-- * Examples
----------------------------------------------------------------------

-- | Example EUF problem
--
-- > f (f (a) − f (b)) = f (c), b >= a, c >= b + c, c >= 0
--
-- from
-- <https://goto.ucsd.edu/~rjhala/classes/sp13/cse291/slides/lec-smt.markdown.pdf>
-- noting that @x >= y@ is the same as @not (x < y)@
example1 :: EUFExpr Tp_Bool
example1 =
  applyOp Op_And
  (applyOp Op_Not
   (applyOp (Op_BVEq knownBVWidth)
    (applyOp f (applyOp f a - applyOp f b))
    (applyOp f c)))
  (applyOp Op_And
   (applyOp Op_Not (applyOp (Op_BVLt knownBVWidth) b a))
   (applyOp Op_And
    (applyOp Op_Not (applyOp (Op_BVLt knownBVWidth) b (b + c)))
    (applyOp Op_Not (applyOp (Op_BVLt knownBVWidth) c (fromInteger 0)))))
  where
    f :: Op '[Tp_BV 32] (Tp_BV 32)
    f = mkUnintOp "f"
    a :: EUFExpr (Tp_BV 32)
    a = mkUnintExpr "a"
    b :: EUFExpr (Tp_BV 32)
    b = mkUnintExpr "b"
    c :: EUFExpr (Tp_BV 32)
    c = mkUnintExpr "c"

-- | Example EUF problem that uses a function with 14 inputs
example2 :: EUFExpr Tp_Bool
example2 =
  applyOp Op_And
  (applyOp
   (Op_BVEq knownBVWidth)
   (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0
    (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 a))
   (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 a))
  (applyOp Op_And
   (applyOp
    (Op_BVEq knownBVWidth)
    a
    (applyOp f14 0 0 0 0 0 0 0 0 0 0 0 0 0 b))
   (applyOp Op_Not
    (applyOp (Op_BVEq knownBVWidth) a b)))
  where
    f14 :: Op '[Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8,
                Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8, Tp_BV 8]
           (Tp_BV 8)
    f14 = mkUnintOp "f"
    a :: EUFExpr (Tp_BV 8)
    a = mkUnintExpr "a"
    b :: EUFExpr (Tp_BV 8)
    b = mkUnintExpr "b"
