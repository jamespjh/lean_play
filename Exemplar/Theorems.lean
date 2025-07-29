import Mathlib.Data.Nat.Basic
set_option pp.parens true

namespace J

theorem def_add_one : ∀ (n m : ℕ),  n + (m + 1) = (n + m) + 1 := by
  intros
  rfl -- this is one of the definitions of addition

theorem zero_add : ∀ n : ℕ, n + 0 = n := by
  intros
  rfl -- this is one of the definitions of addition

theorem add_zero : ∀ n : ℕ, 0 + n = n := by
  intro n
  induction n with
    | zero => rfl
    | succ n hyp => rw [def_add_one 0 n, hyp]

theorem zero_commutative : ∀ n : ℕ, 0 + n = n + 0 := by
  intro n
  rw [add_zero, zero_add]

#check ℕ

theorem add_one_left : ∀ (n m : ℕ),  (n + 1) + m  = (n + m) + 1 := by
  intro n m
  induction m with
    | zero => rfl -- use both definitions of addition
    | succ m ih => rw [def_add_one n m, def_add_one (n+1) m,  ih]

theorem comm : ∀ (n m : ℕ), n + m = m + n := by
  intro n m
  induction n with
    | zero => rw [zero_commutative]
    | succ n ih => rw [add_one_left n m, def_add_one m n, ih]
