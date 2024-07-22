/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Group.Basic

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`).

There is also `Data.Int.Cast.Lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `Data.Int.Cast.Defs` is `Algebra.Group.Basic`.
-/


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]
-- `HasLiftT` appeared in the type signature

@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
  | n + 1, _ => by rw [cast_succ, add_sub_cancel_right]; rfl

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast squash]
theorem cast_negSucc (n : ℕ) : (-[n+1] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.intCast_negSucc n
-- expected `n` to be implicit, and `HasLiftT`

@[simp, norm_cast]
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero
-- type had `HasLiftT`

-- This lemma competes with `Int.ofNat_eq_natCast` to come later
@[simp high, nolint simpNF, norm_cast]
theorem cast_natCast (n : ℕ) : ((n : ℤ) : R) = n :=
  AddGroupWithOne.intCast_ofNat _
-- expected `n` to be implicit, and `HasLiftT`

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast]
theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℤ) : R) = OfNat.ofNat n := by
  simpa only [OfNat.ofNat] using AddGroupWithOne.intCast_ofNat (R := R) n

@[simp, norm_cast]
theorem cast_one : ((1 : ℤ) : R) = 1 := by
  erw [cast_natCast, Nat.cast_one]
-- type had `HasLiftT`

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by erw [cast_natCast, cast_negSucc]
  | -[n+1] => by erw [cast_natCast, cast_negSucc, neg_neg]
-- type had `HasLiftT`

@[simp, norm_cast]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold subNatNat
  cases e : n - m
  · simp only [ofNat_eq_coe]
    simp [e, Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]
-- type had `HasLiftT`

@[simp]
theorem cast_negOfNat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [Int.cast_neg, negOfNat_eq]

@[simp, norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [-Int.natCast_add, ← Int.ofNat_add]
  | (m : ℕ), -[n+1] => by erw [cast_subNatNat, cast_natCast, cast_negSucc, sub_eq_add_neg]
  | -[m+1], (n : ℕ) => by
    erw [cast_subNatNat, cast_natCast, cast_negSucc, sub_eq_iff_eq_add, add_assoc,
      eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] =>
    show (-[m + n + 1+1] : R) = _ by
      rw [cast_negSucc, cast_negSucc, cast_negSucc, ← neg_add_rev, ← Nat.cast_add,
        Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]
-- type had `HasLiftT`

@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]
-- type had `HasLiftT`

theorem cast_two : ((2 : ℤ) : R) = 2 := cast_ofNat _

theorem cast_three : ((3 : ℤ) : R) = 3 := cast_ofNat _

theorem cast_four : ((4 : ℤ) : R) = 4 := cast_ofNat _

end Int
