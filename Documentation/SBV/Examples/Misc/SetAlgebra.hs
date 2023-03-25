-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.SetAlgebra
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves various algebraic properties of sets using SBV. The properties we
-- prove all come from <http://en.wikipedia.org/wiki/Algebra_of_sets>.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.SetAlgebra where

import Data.SBV hiding (complement)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV hiding (complement)
-- >>> import Data.SBV.Set
-- >>> :set -XScopedTypeVariables

-- | Abbreviation for set of integers. For convenience only in monomorphising the properties.
type SI = SSet Integer

-- * Commutativity
{- $commutativity
\(A\cup B=B\cup A\)

>>> prove $ \(a :: SI) b -> a `union` b .== b `union` a
Q.E.D.

\(A\cap B=B\cap A\)

>>> prove $ \(a :: SI) b -> a `intersection` b .== b `intersection` a
Q.E.D.
-}

-- * Associativity
{- $associativity

\((A\cup B)\cup C=A\cup (B\cup C)\)

>>> prove $ \(a :: SI) b c -> a `union` (b `union` c) .== (a `union` b) `union` c
Q.E.D.

\((A\cap B)\cap C=A\cap (B\cap C)\)

>>> prove $ \(a :: SI) b c -> a `intersection` (b `intersection` c) .== (a `intersection` b) `intersection` c
Q.E.D.
-}

-- * Distributivity
{- $distributivity
\(A\cup (B\cap C)=(A\cup B)\cap (A\cup C)\)

>>> prove $ \(a :: SI) b c -> a `union` (b `intersection` c) .== (a `union` b) `intersection` (a `union` c)
Q.E.D.

\(A\cap (B\cup C)=(A\cap B)\cup (A\cap C)\)

>>> prove $ \(a :: SI) b c -> a `intersection` (b `union` c) .== (a `intersection` b) `union` (a `intersection` c)
Q.E.D.
-}

-- * Identity properties
{- $identity

\(A\cup \varnothing = A\)

>>> prove $ \(a :: SI) -> a `union` empty .== a
Q.E.D.

\(A\cap U = A \)

>>> prove $ \(a :: SI) -> a `intersection` full .== a
Q.E.D.
-}

-- * Complement properties
{- $complement

\( A\cup A^{C}=U \)

>>> prove $ \(a :: SI) -> a `union` complement a .== full
Q.E.D.

\( A\cap A^{C}=\varnothing \)

>>> prove $ \(a :: SI) -> a `intersection` complement a .== empty
Q.E.D.

\({(A^{C})}^{C}=A\)

>>> prove $ \(a :: SI) -> complement (complement a) .== a
Q.E.D.

\(\varnothing ^{C}=U\)

>>> prove $ complement (empty :: SI) .== full
Q.E.D.

\( U^{C}=\varnothing \)

>>> prove $ complement (full :: SI) .== empty
Q.E.D.
-}

-- * Uniqueness of the complement
--
{- $compUnique
The complement of a set is the only set that satisfies the first two complement properties above. That
is complementation is characterized by those two laws, as we can formally establish:

\( A\cup B=U \land A\cap B=\varnothing \iff B=A^{C} \)

>>> prove $ \(a :: SI) b -> a `union` b .== full .&& a `intersection` b .== empty .<=> b .== complement a
Q.E.D.
-}

-- * Idempotency
{- $idempotent

\( A\cup A=A \)

>>> prove $ \(a :: SI) -> a `union` a .== a
Q.E.D.

\( A\cap A=A \)

>>> prove $ \(a :: SI) -> a `intersection` a .== a
Q.E.D.
-}

-- * Domination properties
{- $domination

\( A\cup U=U \)

>>> prove $ \(a :: SI) -> a `union` full .== full
Q.E.D.

\( A\cap \varnothing =\varnothing \)

>>> prove $ \(a :: SI) -> a `intersection` empty .== empty
Q.E.D.
-}

-- * Absorption properties
{- $absorption

\( A\cup (A\cap B)=A \)

>>> prove $ \(a :: SI) b -> a `union` (a `intersection` b) .== a
Q.E.D.

\( A\cap (A\cup B)=A \)

>>> prove $ \(a :: SI) b -> a `intersection` (a `union` b) .== a
Q.E.D.
-}

-- * Intersection and set difference
{- $intdiff

\( A\cap B=A\setminus (A\setminus B) \)

>>> prove $ \(a :: SI) b -> a `intersection` b .== a `difference` (a `difference` b)
Q.E.D.
-}

-- * De Morgan's laws
{- $deMorgan

\( (A\cup B)^{C}=A^{C}\cap B^{C} \)

>>> prove $ \(a :: SI) b -> complement (a `union` b) .== complement a `intersection` complement b
Q.E.D.

\( (A\cap B)^{C}=A^{C}\cup B^{C} \)

>>> prove $ \(a :: SI) b -> complement (a `intersection` b) .== complement a `union` complement b
Q.E.D.
-}

-- * Inclusion is a partial order
{- $incPO
Subset inclusion is a partial order, i.e., it is reflexive, antisymmetric, and transitive:

\( A \subseteq A \)

>>> prove $ \(a :: SI) -> a `isSubsetOf` a
Q.E.D.

\( A\subseteq B \land B\subseteq A \iff A = B \)

>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .&& b `isSubsetOf` a .<=> a .== b
Q.E.D.

\( A\subseteq B \land B\subseteq C \Rightarrow A \subseteq C \)

>>> prove $ \(a :: SI) b c -> a `isSubsetOf` b .&& b `isSubsetOf` c .=> a `isSubsetOf` c
Q.E.D.
-}

-- * Joins and meets
{- $joinMeet

\( A\subseteq A\cup B \)

>>> prove $ \(a :: SI) b -> a `isSubsetOf` (a `union` b)
Q.E.D.


\( A\subseteq C \land B\subseteq C \Rightarrow (A \cup B) \subseteq C \)

>>> prove $ \(a :: SI) b c -> a `isSubsetOf` c .&& b `isSubsetOf` c .=> (a `union` b) `isSubsetOf` c
Q.E.D.

\( A\cap B\subseteq A \)

>>> prove $ \(a :: SI) b -> (a `intersection` b) `isSubsetOf` a
Q.E.D.

\( A\cap B\subseteq B \)

>>> prove $ \(a :: SI) b -> (a `intersection` b) `isSubsetOf` b
Q.E.D.

\( C\subseteq A \land C\subseteq B \Rightarrow C \subseteq (A \cap B) \)

>>> prove $ \(a :: SI) b c -> c `isSubsetOf` a .&& c `isSubsetOf` b .=> c `isSubsetOf` (a `intersection` b)
Q.E.D.
-}

-- * Subset characterization
{- $subsetChar
There are multiple equivalent ways of characterizing the subset relationship:

\( A\subseteq B  \iff A \cap B = A \) 

>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> a `intersection` b .== a
Q.E.D.


\( A\subseteq B \iff A \cup B = B \) 

>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> a `union` b .== b
Q.E.D.

\( A\subseteq B \iff A \setminus B = \varnothing \)

>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> a `difference` b .== empty
Q.E.D.

\( A\subseteq B \iff B^{C} \subseteq A^{C} \)

>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> complement b `isSubsetOf` complement a
Q.E.D.
-}

-- * Relative complements
{- $relComp

\( C\setminus (A\cap B)=(C\setminus A)\cup (C\setminus B) \)

>>> prove $ \(a :: SI) b c -> c \\ (a `intersection` b) .== (c \\ a) `union` (c \\ b)
Q.E.D.

\( C\setminus (A\cup B)=(C\setminus A)\cap (C\setminus B) \)

>>> prove $ \(a :: SI) b c -> c \\ (a `union` b) .== (c \\ a) `intersection` (c \\ b)
Q.E.D.


\( \displaystyle C\setminus (B\setminus A)=(A\cap C)\cup (C\setminus B) \)

>>> prove $ \(a :: SI) b c -> c \\ (b \\ a) .== (a `intersection` c) `union` (c \\ b)
Q.E.D.

\( (B\setminus A)\cap C = (B\cap C)\setminus A \)

>>> prove $ \(a :: SI) b c -> (b \\ a) `intersection` c .== (b `intersection` c) \\ a
Q.E.D.

\( (B\setminus A)\cap C= B\cap (C\setminus A) \)

>>> prove $ \(a :: SI) b c -> (b \\ a) `intersection` c .== b `intersection` (c \\ a)
Q.E.D.

\( (B\setminus A)\cup C=(B\cup C)\setminus (A\setminus C) \)

>>> prove $ \(a :: SI) b c -> (b \\ a) `union` c .== (b `union` c) \\ (a \\ c)
Q.E.D.


\( A \setminus A = \varnothing \)

>>> prove $ \(a :: SI) -> a \\ a .== empty
Q.E.D.

\( \varnothing \setminus A = \varnothing \)

>>> prove $ \(a :: SI) -> empty \\ a .== empty
Q.E.D.

\( A \setminus \varnothing = A \)

>>> prove $ \(a :: SI) -> a \\ empty .== a
Q.E.D.

\( B \setminus A = A^{C} \cap B \)

>>> prove $ \(a :: SI) b -> b \\ a .== complement a `intersection` b
Q.E.D.

\( {(B \setminus A)}^{C} = A \cup B^{C} \)

>>> prove $ \(a :: SI) b -> complement (b \\ a) .== a `union` complement b
Q.E.D.

\( U \setminus A = A^{C} \)

>>> prove $ \(a :: SI) -> full \\ a .== complement a
Q.E.D.


\( A \setminus U = \varnothing \)

>>> prove $ \(a :: SI) -> a \\ full .== empty
Q.E.D.
-}

-- * Distributing subset relation
{- $distSubset

A common mistake newcomers to set theory make is to distribute the subset relationship over intersection
and unions, which is only true as described above. Here, we use SBV to show two incorrect cases:

Subset relation does /not/ distribute over union on the left:

\(A \subseteq (B \cup C) \nRightarrow A \subseteq B \land A \subseteq C \)

>>> prove $ \(a :: SI) b c -> a `isSubsetOf` (b `union` c) .=> a `isSubsetOf` b .&& a `isSubsetOf` c
Falsifiable. Counter-example:
  s0 =     {2} :: {Integer}
  s1 =       U :: {Integer}
  s2 = U - {2} :: {Integer}

Similarly, subset relation does /not/ distribute over intersection on the right:

\( (B \cap C) \subseteq A \nRightarrow B \subseteq A \land C \subseteq A \)

>>> prove $ \(a :: SI) b c -> (b `intersection` c) `isSubsetOf` a .=> b `isSubsetOf` a .&& c `isSubsetOf` a
Falsifiable. Counter-example:
  s0 = U - {2} :: {Integer}
  s1 =      {} :: {Integer}
  s2 =     {2} :: {Integer}
-}
