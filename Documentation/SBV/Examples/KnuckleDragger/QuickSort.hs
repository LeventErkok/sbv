-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.QuickSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving quick sort correct.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.QuickSort where

{-
theory QuickSort_Standalone
begin

(* Define natural numbers *)
datatype nat = Z | S nat

(* Define addition on nat *)
fun add :: "nat ⇒ nat ⇒ nat" where
  "add Z n = n"
| "add (S m) n = S (add m n)"

(* Define integers as an abstract type (for simplicity, assume they exist) *)
typedecl int

consts
  le :: "int ⇒ int ⇒ bool" (infix "≤" 50)
  lt :: "int ⇒ int ⇒ bool" (infix "<" 50)
  eq :: "int ⇒ int ⇒ bool" (infix "=" 50)

axiomatization where
  le_refl: "x ≤ x" and
  le_trans: "x ≤ y ⟹ y ≤ z ⟹ x ≤ z" and
  le_antisym: "x ≤ y ⟹ y ≤ x ⟹ x = y" and
  le_lt: "x ≤ y ⟷ (x < y ∨ x = y)"

(* Define lists *)
datatype 'a list = Nil | Cons 'a "'a list"

(* Append *)
fun app :: "'a list ⇒ 'a list ⇒ 'a list" (infixr "@" 65) where
  "Nil @ ys = ys"
| "Cons x xs @ ys = Cons x (xs @ ys)"

(* Filter function *)
fun filter :: "('a ⇒ bool) ⇒ 'a list ⇒ 'a list" where
  "filter P Nil = Nil"
| "filter P (Cons x xs) = (if P x then Cons x (filter P xs) else filter P xs)"

(* Count: number of times x appears in list *)
fun count :: "'a ⇒ 'a list ⇒ nat" where
  "count x Nil = Z"
| "count x (Cons y ys) = (if x = y then S (count x ys) else count x ys)"

(* Permutation: equal counts of all elements *)
definition perm :: "'a list ⇒ 'a list ⇒ bool" where
  "perm xs ys ⟷ (∀x. count x xs = count x ys)"

(* Sorted predicate *)
fun sorted :: "int list ⇒ bool" where
  "sorted Nil = True"
| "sorted (Cons x Nil) = True"
| "sorted (Cons x (Cons y ys)) = (x ≤ y ∧ sorted (Cons y ys))"

(* Quicksort definition *)
fun quicksort :: "int list ⇒ int list" where
  "quicksort Nil = Nil"
| "quicksort (Cons x xs) = 
     quicksort (filter (λy. y ≤ x) xs) @ 
     Cons x (quicksort (filter (λy. x < y) xs))"

(* Lemmas to support main theorem *)
lemma count_app: "count x (xs @ ys) = add (count x xs) (count x ys)"
  apply (induction xs)
   apply auto
  done

lemma count_filter_le:
  "count x (filter (λy. y ≤ z) xs) = (if x ≤ z then count x xs else Z)"
  apply (induction xs)
   apply auto
  done

lemma count_filter_gt:
  "count x (filter (λy. z < y) xs) = (if z < x then count x xs else Z)"
  apply (induction xs)
   apply auto
  done

theorem quicksort_perm: "perm (quicksort xs) xs"
proof (induction xs)
  case Nil
  then show ?case by (simp add: perm_def)
next
  case (Cons x xs)
  let ?L = "filter (λy. y ≤ x) xs"
  let ?R = "filter (λy. x < y) xs"
  have "perm (quicksort xs) (quicksort ?L @ Cons x (quicksort ?R))" by simp
  also have "perm … (?L @ Cons x ?R)"
    using Cons.IH by (auto simp: perm_def count_app count_filter_le count_filter_gt)
  also have "perm … (Cons x xs)"
    unfolding perm_def
    by (auto simp: count.simps count_filter_le count_filter_gt count_app)
  finally show ?case .
qed

theorem quicksort_sorted: "sorted (quicksort xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?L = "quicksort (filter (λy. y ≤ x) xs)"
  let ?R = "quicksort (filter (λy. x < y) xs)"
  have L: "sorted ?L" using Cons.IH(1) by simp
  have R: "sorted ?R" using Cons.IH(2) by simp
  show ?case
  proof (cases ?L)
    case Nil
    then show ?thesis using R by simp
  next
    case (Cons l1 lxs)
    have "sorted (?L @ Cons x ?R)" using L R
      by (auto simp: sorted.simps)
    then show ?thesis by simp
  qed
qed

end
-}
