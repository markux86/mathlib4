/-
Copyright (c) 2024 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib

open Polynomial

/-!
# L'Hôpital's Rule for Polynomials over Arbitrary Fields

This file proves an analogue of l'Hôpital's Rule for polynomials over arbitrary fields,
based on the work of Chalkias et al. (https://eprint.iacr.org/2024/1279.pdf).
The main result states that if `f(x) = g(x)h(x)` and both `f(α) = 0` and `g(α) = 0`,
then `f'(α) = g'(α)h(α)`.
-/

variable {F : Type*} [Field F]

-- Lemma 1
/-- Given a polynomial `f` and a root `α`, there exists a unique polynomial `fα `
such that `f(x) = fα(x)(x - α)`. -/
theorem exists_unique_factor {f : F[X]} {α : F} (hf : eval α f = 0) :
  ∃! fα : F[X], f = fα * (X - C α) := by
  -- Establish that (X - C α) is monic
  have h_monic : Monic (X - C α) := monic_X_sub_C α
  -- Get quotient q and remainder r
  let q := f /ₘ (X - C α)
  let r := f %ₘ (X - C α)
  -- Rewrite f in terms of q and r
  have h_div : f = r + (X - C α) * q := (modByMonic_add_div f h_monic).symm
  have h_deg : degree r < degree (X - C α) := degree_modByMonic_lt f h_monic
  have h_deg_X_sub_C : degree (X - C α) = 1 := degree_X_sub_C α
  -- Therefore degree r < 1
  have h_deg_lt_one : degree r < 1 := by
    rw [h_deg_X_sub_C] at h_deg
    exact h_deg
  -- Thus, r is constant
  have r_constant : r.degree ≤ 0 := by
    exact Nat.WithBot.lt_one_iff_le_zero.mp h_deg_lt_one
  -- Thus, r evaluates to 0 at α
  rw [h_div] at hf
  rw [eval_add, eval_mul, eval_sub, eval_X, eval_C] at hf
  simp at hf
  -- As r is constant and evaluates to 0, it must be the zero polynomial
  have r_eq_zero : r = 0 := by
    have h : r = C (coeff r 0) := eq_C_of_degree_le_zero r_constant
    rw [h] at hf
    simp at hf
    rw [h]
    simp [hf]
  -- Consequently, get rid of r
  rw [h_div, r_eq_zero, zero_add]
  -- Show that there is a unique q = fα
  use q
  constructor
  · -- (Existence) Show q satisfies the equation
    exact CommMonoid.mul_comm (X - C α) q
  · -- (Uniqueness) Any other y satisfying the equation must equal q
    intro y h_eq
    rw [CommMonoid.mul_comm y (X - C α)] at h_eq
    exact mul_left_cancel₀ (Monic.ne_zero h_monic) (Eq.symm h_eq)

--Lemma 2
/-- Given a polynomial `f` such that `f(0)=0`,
    then `f'(0)=f₀(0)` where `f₀` is the polynomial `fα` with `α=0` from Lemma 1. -/
lemma derivative_zero_eq_factor_zero (f : F[X])
    (h : f.eval 0 = 0) :
    (derivative f).eval 0 = (f.div (X - C 0)).eval 0 := by
    sorry

-- Corollary 1
/-- Given a polynomial `f` such that `f(α)=0`, then `f'(α)=fα(α)`. -/
theorem derivative_eval_eq_factor_eval (f : F[X]) (α : F)
    (h : f.eval α = 0) :
    (derivative f).eval α = (f.div (X - C α)).eval α := by
    sorry

-- Main Theorem (L'Hôpital's Rule for Polynomials)
/-- Given polynomials f, g, h such that `f(x)=g(x)h(x)` and `f(α)=g(α)=0`,
then `f'(α)=g'(α)h(α)`. -/
theorem lhopital_rule_polynomials (f g h : F[X]) (α : F)
    (hf : f = g * h) (hfα : f.eval α = 0) (hgα : g.eval α = 0) :
    (derivative f).eval α = (derivative g).eval α * h.eval α := by
    sorry
