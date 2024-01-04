-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.FirstOrderLogic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves various first-order logic properties using SBV. The properties we
-- prove all come from <https://en.wikipedia.org/wiki/First-order_logic>
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

#if MIN_VERSION_base(4,19,0)
{-# LANGUAGE TypeAbstractions    #-}
#endif

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.FirstOrderLogic where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only, ignore.
-- >>> import Data.SBV
-- >>> :set -XDataKinds

-- | An uninterpreted sort for demo purposes, named 'U'
data U
mkUninterpretedSort ''U

-- | An uninterpreted sort for demo purposes, named 'V'
data V
mkUninterpretedSort ''V

-- | An enumerated type for demo purposes, named 'E'
data E = A | B | C
mkSymbolicEnumeration ''E

-- | Helper to turn quantified formula to a regular boolean. We
-- can think of this as quantifier elimination, hence the name 'qe'.
qe :: QuantifiedBool a => a -> SBool
qe = quantifiedBool

-- * Pushing negation over quantifiers
{- $negUniv
\(\lnot \forall x\,P(x)\Leftrightarrow \exists x\,\lnot P(x)\)

>>> let p = uninterpret "P" :: SU -> SBool
>>> prove $ sNot (qe (\(Forall x) -> p x)) .<=> qe (\(Exists x) -> sNot (p x))
Q.E.D.

\(\lnot \exists x\,P(x)\Leftrightarrow \forall x\,\lnot P(x)\)

>>> let p = uninterpret "P" :: SU -> SBool
>>> prove $ sNot (qe (\(Exists x) -> p x)) .<=> qe (\(Forall x) -> sNot (p x))
Q.E.D.
-}

-- * Interchanging quantifiers
{- $interchange
\(\forall x\,\forall y\,P(x,y)\Leftrightarrow \forall y\,\forall x\,P(x,y)\)

>>> let p = uninterpret "P" :: (SU, SV) -> SBool
>>> prove $ qe (\(Forall x) (Forall y) -> p (x, y)) .<=> qe (\(Forall y) (Forall x) -> p (x, y))
Q.E.D.

\(\exists x\,\exists y\,P(x,y)\Leftrightarrow \exists y\,\exists x\,P(x,y)\)

>>> let p = uninterpret "P" :: (SU, SV) -> SBool
>>> prove $ qe (\(Exists x) (Exists y) -> p (x, y)) .<=> qe (\(Exists y) (Exists x) -> p (x, y))
Q.E.D.
-}

-- * Merging quantifiers
{- $mergeQuants
\(\forall x\,P(x)\land \forall x\,Q(x)\Leftrightarrow \forall x\,(P(x)\land Q(x))\)

>>> let p = uninterpret "P" :: SU -> SBool
>>> let q = uninterpret "Q" :: SU -> SBool
>>> prove $ (qe (\(Forall x) -> p x) .&& qe (\(Forall x) -> q x)) .<=> qe (\(Forall x) -> p x .&& q x)
Q.E.D.

\(\exists x\,P(x)\lor \exists x\,Q(x)\Leftrightarrow \exists x\,(P(x)\lor Q(x))\)

>>> let p = uninterpret "P" :: SU -> SBool
>>> let q = uninterpret "Q" :: SU -> SBool
>>> prove $ (qe (\(Exists x) -> p x) .|| qe (\(Exists x) -> q x)) .<=> qe (\(Exists x) -> p x .|| q x)
Q.E.D.
-}

-- * Scoping over quantifiers
{- $scopeOverQuants
Provided \(x\) is not free in \(P\): \(P\land \exists x\,Q(x)\Leftrightarrow \exists x\,(P\land Q(x))\)

>>> let p = uninterpret "P" :: SBool
>>> let q = uninterpret "Q" :: SU -> SBool
>>> prove $ (p .&& qe (\(Exists x) -> q x)) .<=> qe (\(Exists x) -> p .&& q x)
Q.E.D.

Provided \(x\) is not free in \(P\): \(P\lor \forall x\,Q(x)\Leftrightarrow \forall x\,(P\lor Q(x))\)

>>> let p = uninterpret "P" :: SBool
>>> let q = uninterpret "Q" :: SU -> SBool
>>> prove $ (p .|| qe (\(Forall x) -> q x)) .<=> qe (\(Forall x) -> p .|| q x)
Q.E.D.
-}

-- * A non-identity
{- $nonIdentity
It's instructive to look at an example where the proof actually fails. Consider, for instance, an
example of a merging quantifiers like we did above, except when the equality doesn't hold. That
is, we try to prove the "correct" sounding, but incorrect conjecture:

\(\forall x\,P(x)\lor \forall x\,Q(x)\Leftrightarrow \forall x\,(P(x)\lor Q(x))\)

We have:

>>> let p = uninterpret "P" :: SU -> SBool
>>> let q = uninterpret "Q" :: SU -> SBool
>>> prove $ (qe (\(Forall x) -> p x) .|| qe (\(Forall x) -> q x)) .<=> qe (\(Forall x) -> p x .|| q x)
Falsifiable. Counter-example:
  P :: U -> Bool
  P U!val!2 = True
  P U!val!0 = True
  P _       = False
<BLANKLINE>
  Q :: U -> Bool
  Q U!val!2 = False
  Q U!val!0 = False
  Q _       = True

The solver found us a falsifying instance: Pick a domain with at least three elements. We'll call
the first element @U!val!2@, and the second element @U!val!0@, without naming the others. (Unfortunately the solver picks nonintuitive names, but you can substitute better names if you like. They're just names of two distinct
objects that belong to the domain \(U\) with no other meaning.)

Arrange so that \(P\) is true on @U!val!2@ and @U!val!0@, but false for everything else.
Also arrange so that \(Q\) is false on these two elements, but true for everything else.

With this
assignment, the right hand side of our conjecture
is true no matter which element you pick, because either \(P\) or \(Q\) is true on any
given element. (Actually, only one will be true on any element, but that is tangential.)
But left-hand-side is not a tautology: Clearly neither \(P\) nor \(Q\) are true for all elements, and
hence both disjuncts are false. Thus, the alleged conjecture is not an equivalence in first order logic.
-}

-- * Exists unique
{- $existsUnique
We can use the 'ExistsUnique' constructor to indicate a value must exists uniquely. For instance,
we can prove that there is an element in 'E' that's less than 'C', but it's not unique. However,
there's a unique element that's less than all the elements in 'E':

>>> prove $ \(Exists       (me :: SE)) -> me .<= sC
Q.E.D.
>>> prove $ \(ExistsUnique (me :: SE)) -> me .<= sC
Falsifiable
>>> prove $ \(ExistsUnique (me :: SE)) (Forall e) -> me .<= e
Q.E.D.
-}

-- * Skolemization
{- $skolemization
Given a formula, skolemization produces an equisatisfiable formula that has no existential quantifiers. Instead,
the existentials are replaced by uninterpreted functions.
Skolemization is useful when we want to see the instantiation of nested existential variables. Interpretation for such variables will be
functions of the enclosing universals.
-}

-- | Consider the formula \(\forall x\,\exists y\, x \ge y\), over bit-vectors of size 8. We can ask SBV to satisfy it:
--
-- >>> sat skolemEx1
-- Satisfiable
--
-- But this isn't really illimunating. We can first skolemize, and then ask to satisfy:
--
-- >>> sat $ skolemize skolemEx1
-- Satisfiable. Model:
--   y :: Word8 -> Word8
--   y x = x
--
-- which is much better We are told that we can have the witness as the value given for each choice of @x@.
skolemEx1 :: Forall "x" Word8 -> Exists "y" Word8 -> SBool
skolemEx1 (Forall x) (Exists y) = x .>= y

-- | Consider the formula \(\forall a\,\exists b\,\forall c\,\exists d\, a + b >= c + d\), over bit-vectors of size 8. We can ask SBV to satisfy it:
--
-- >>> sat skolemEx2
-- Satisfiable
--
-- Again, we're left in the dark as to why this is satisfiable. Let's skolemize first, and then call 'sat' on it:
--
-- >>> sat $ skolemize skolemEx2
-- Satisfiable. Model:
--   b :: Word8 -> Word8
--   b _ = 0
-- <BLANKLINE>
--   d :: Word8 -> Word8 -> Word8
--   d a c = a + 255 * c
--
-- Let's see what the solver said. It suggested we should use the value of @0@ for @b@, regardless of the
-- choice of @a@. (Note how @b@ is a function of one variable, i.e., of @a@)
-- And it suggested using @a + (255 * c)@ for @d@,
-- for whatever we choose for @a@ and @c@. Why does this work? Well, given
-- arbitrary @a@ and @c@, we end up with:
--
-- @
--     a + b >= c + d
--     --> substitute b = 0 and d = a + 255c as suggested by the solver
--     a + 0 >= c + a + 255c
--     a >= 256c + a
--     a >= a
-- @
--
-- showing the formula is satisfiable for whatever values you pick for @a@ and @c@. Note that @256@ is simply
-- @0@ when interpreted modulo @2^8@. Clever!
skolemEx2 :: Forall "a" Word8 -> Exists "b" Word8 -> Forall "c" Word8 -> Exists "d" Word8 -> SBool
skolemEx2 (Forall a) (Exists b) (Forall c) (Exists d) = a + b .>= c + d

-- | A common proof technique to show validity is to show that the negation is unsatisfiable. Note
-- that if you want to skolemize during this process, you should first /negate/ and then skolemize!
--
-- This example demonstrates the possible pitfall. The 'skolemEx3' function
-- encodes \(\exists x\, \forall y\, y \ge x\) for 8-bit bitvectors; which is a valid statement since
-- @x = 0@ acts as the witness. We can directly prove this in SBV:
--
-- >>> prove skolemEx3
-- Q.E.D.
--
-- Or, we can ask if the negation is unsatisfiable:
--
-- >>> sat (qNot skolemEx3)
-- Unsatisfiable
--
-- If we want, we can skolemize after the negation step:
--
-- >>> sat (skolemize (qNot skolemEx3))
-- Unsatisfiable
--
-- and get the same result. However, it would be __unsound__ to skolemize first and then negate:
--
-- >>> sat (qNot (skolemize skolemEx3))
-- Satisfiable. Model:
--   x = 1 :: Word8
--
-- And that would be the incorrect conclusion that our formula is invalid with a counter-example! You
-- can see the same by doing:
--
-- >>> prove (skolemize skolemEx3)
-- Falsifiable. Counter-example:
--   x = 1 :: Word8
--
-- So, if you want to check validity and want to also perform skolemization; you should negate your
-- formula first and then skolemize, not the other way around!
skolemEx3 :: Exists "x" Word8 -> Forall "y" Word8 -> SBool
skolemEx3 (Exists x) (Forall y) = y .>= x

-- | If you skolemize different formulas that share the same name for their existentials, then SBV will
-- get confused and will think those represent the same skolem function. This is unfortunate, but it follows
-- the requirement that uninterpreted function names should be unique. In this particular case, however, since
-- SBV creates these functions, it is harder to control the internal names. In such cases, use the function
-- 'taggedSkolemize' to provide a name to prefix the skolem functions. As demonstrated by 'skolemEx4'. We get:
--
-- >>> skolemEx4
-- Satisfiable. Model:
--   c1_y :: Integer -> Integer
--   c1_y x = x
-- <BLANKLINE>
--   c2_y :: Integer -> Integer
--   c2_y x = x + 1
--
-- Note how the internal skolem functions are named according to the tag given. If you use regular 'skolemize'
-- this program will essentially do the wrong thing by assuming the skolem functions for both predicates are
-- the same, and will return unsat. Beware!
-- All skolem functions should be named differently in your program for your deductions to be sound.
skolemEx4 :: IO SatResult
skolemEx4 = sat cs
  where cs :: ConstraintSet
        cs = do constrain $ taggedSkolemize "c1" $ \(Forall @"x" x) (Exists @"y" y) -> x .== (y   :: SInteger)
                constrain $ taggedSkolemize "c2" $ \(Forall @"x" x) (Exists @"y" y) -> x .== (y-1 :: SInteger)

-- * Special relations

-- ** Partial orders
{- $partialOrder
A partial order is a reflexive, antisymmetic, and a transitive relation. We can prove these properties
for relations that are checked by the 'isPartialOrder' predicate in SBV:

\(\forall x\,R(x,x)\)

\(\forall x\,\forall y\, R(x, y) \land R(y, x) \Rightarrow x = y\)

\(\forall x\,\forall y\, \forall z\, R(x, y) \land R(y, z) \Rightarrow R(x, z)\)

>>> let r         = uninterpret "R" :: Relation U
>>> let isPartial = isPartialOrder "poR" r
>>> prove $ \(Forall x) -> isPartial .=> r (x, x)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) -> isPartial .=> (r (x, y) .&& r (y, x) .=> x .== y)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isPartial .=> (r (x, y) .&& r (y, z) .=> r (x, z))
Q.E.D.
-}

-- | Demonstrates creating a partial order. We have:
--
-- >>> poExample
-- Q.E.D.
poExample :: IO ThmResult
poExample = prove $ do
  let r = uninterpret "R" :: Relation E
  constrain $ isPartialOrder "poR" r

  pure $ qe (\(Forall x) -> r (x, x)) :: Predicate

-- ** Linear orders
{- $linearOrder
A linear order, ensured by the predicate 'isLinearOrder', satisfies the following axioms:

\(\forall x\,R(x,x)\)

\(\forall x\,\forall y\, R(x, y) \land R(y, x) \Rightarrow x = y\)

\(\forall x\,\forall y\, \forall z\, R(x, y) \land R(y, z) \Rightarrow R(x, z)\)

\(\forall x\,\forall y\, R(x, y) \lor R(y, x)\)

>>> let r        = uninterpret "R" :: Relation U
>>> let isLinear = isLinearOrder "loR" r
>>> prove $ \(Forall x) -> isLinear .=> r (x, x)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) -> isLinear .=> (r (x, y) .&& r (y, x) .=> x .== y)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isLinear .=> (r (x, y) .&& r (y, z) .=> r (x, z))
Q.E.D.
>>> prove $ \(Forall x) (Forall y) -> isLinear .=> (r (x, y) .|| r (y, x))
Q.E.D.
-}

-- ** Tree orders
{- $treeOrder
A tree order, ensured by the predicate 'isTreeOrder', satisfies the following axioms:

\(\forall x\,R(x,x)\)

\(\forall x\,\forall y\, R(x, y) \land R(y, x) \Rightarrow x = y\)

\(\forall x\,\forall y\, \forall z\, R(x, y) \land R(y, z) \Rightarrow R(x, z)\)

\(\forall x\,\forall y\,\forall z\, (R(y, x) \land R(z, z)) \Rightarrow (R (y, z) \lor R (z, y))\)

>>> let r      = uninterpret "R" :: Relation U
>>> let isTree = isTreeOrder "toR" r
>>> prove $ \(Forall x) -> isTree .=> r (x, x)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) -> isTree .=> (r (x, y) .&& r (y, x) .=> x .== y)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isTree .=> (r (x, y) .&& r (y, z) .=> r (x, z))
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isTree .=> ((r (y, x) .&& r (z, x)) .=> (r (y, z) .|| r (z, y)))
Q.E.D.
-}

-- ** Piecewise linear orders
{- $piecewiseLinear
A piecewise linear order, ensured by the predicate 'isPiecewiseLinearOrder', satisfies the following axioms:

\(\forall x\,R(x,x)\)

\(\forall x\,\forall y\, R(x, y) \land R(y, x) \Rightarrow x = y\)

\(\forall x\,\forall y\, \forall z\, R(x, y) \land R(y, z) \Rightarrow R(x, z)\)

\(\forall x\,\forall y\,\forall z\, (R(x, y) \land R(x, z)) \Rightarrow (R (y, z) \lor R (z, y))\)

\(\forall x\,\forall y\,\forall z\, (R(y, x) \land R(z, x)) \Rightarrow (R (y, z) \lor R (z, y))\)

>>> let r           = uninterpret "R" :: Relation U
>>> let isPiecewise = isPiecewiseLinearOrder "plR" r
>>> prove $ \(Forall x) -> isPiecewise .=> r (x, x)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) -> isPiecewise .=> (r (x, y) .&& r (y, x) .=> x .== y)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isPiecewise .=> (r (x, y) .&& r (y, z) .=> r (x, z))
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isPiecewise .=> ((r (x, y) .&& r (x, z)) .=> (r (y, z) .|| r (z, y)))
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> isPiecewise .=> ((r (y, x) .&& r (z, x)) .=> (r (y, z) .|| r (z, y)))
Q.E.D.
-}

-- ** Transitive closures
{- $transitiveClosures
The transitive closure of a relation can be created using 'mkTransitiveClosure'. Transitive closures
are not first-order axiomatizable. That is, we cannot write first-order formulas to uniquely
describe them. However, we can check some of the expected properties:

>>> let r   = uninterpret "R" :: Relation U
>>> let tcR = mkTransitiveClosure "tcR" r
>>> prove $ \(Forall x) (Forall y) -> r (x, y) .=> tcR (x, y)
Q.E.D.
>>> prove $ \(Forall x) (Forall y) (Forall z) -> r (x, y) .&& r (y, z) .=> tcR (x, z)
Q.E.D.

What's missing here is the check that if the transitive closure relates two elements, then they are
connected transitively in the original relation. This requirement is not axiomatizable in first order logic.
-}

-- | Create a transitive relation of a simple relation and show that transitive connections are respected.
-- We have:
--
-- >>> tcExample1
-- Q.E.D.
tcExample1 :: IO ThmResult
tcExample1 = prove $ do
  a :: SU <- free "a"
  b :: SU <- free "b"
  c :: SU <- free "c"

  let r   = uninterpret "R"
      tcR = mkTransitiveClosure "tcR" r

  -- Add R(a, b), R(b, c), but explicitly state ~R(a, c)
  constrain $ r (a, b)
  constrain $ r (b, c)
  constrain $ sNot $ r (a, c)

  -- Show that in tcR, a and c are connected
  pure $ tcR (a, c)

-- | Another transitive-closure example, this time we show the transitive closure is the smallest
-- relation, i.e., doesn't have extra connections. We have:
--
-- >>> tcExample2
-- Q.E.D.
tcExample2 :: IO ThmResult
tcExample2 = prove $ do
  let r   = uninterpret "r"
      tcR = mkTransitiveClosure "tcR" r

  -- Add R(A, B), ~R(A, C), ~R(B, C) then it shouldn't be the case that R(a, c)
  constrain $ r (sA, sB)
  constrain $ sNot $ r (sA, sC)
  constrain $ sNot $ r (sB, sC)

  -- Show that in tcR, a and c cannot be connected
  pure $ sNot $ tcR (sA, sC) :: Predicate

-- | Demonstrates computing the transitive closure of existing relations. We have:
--
-- >>> tcExample3
-- Q.E.D.
tcExample3 :: IO ThmResult
tcExample3 = prove $ do

        -- Define a relation over the type 'E', which only relates 'A' to 'B'.
        let rel :: Relation E
            rel xy = xy .== (sA, sB)

        -- Create a relation and its transitive closure, and associate it with our function:
        let tcR = mkTransitiveClosure "R" rel

        -- Show that in tcR, a and c cannot be connected
        pure $ sNot $ tcR (sA, sC) :: Predicate
