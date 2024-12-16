/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
  # Docs
-/


section

open Asymptotics Filter

theorem Asymptotics.isEquivalent_nat_floor {R : Type*} [NormedLinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    (fun (x : R) ↦ ↑⌊x⌋₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards with x hx
    rw [hx, Nat.floor_zero, Nat.cast_eq_zero]
  · exact tendsto_nat_floor_div_atTop

theorem Asymptotics.isEquivalent_nat_ceil {R : Type*} [NormedLinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    (fun (x : R) ↦ ↑⌈x⌉₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards with x hx
    rw [hx, Nat.ceil_zero, Nat.cast_eq_zero]
  · exact tendsto_nat_ceil_div_atTop

end

open Finset Filter MeasureTheory Topology Complex

private theorem aux1 {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (deriv fun (t : ℝ) ↦ (t : ℂ) ^ (-s)) (Set.Ici 1) := by
  have h_int : IntegrableOn (fun x ↦ Complex.abs (-s) * x ^ (-s - 1).re) (Set.Ici 1) := by
    refine Integrable.const_mul (integrableOn_Ici_iff_integrableOn_Ioi.mpr
      ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr ?_)) _
    rwa [sub_re, neg_re, one_re, sub_lt_iff_lt_add, neg_add_cancel, neg_lt_zero]
  refine (integrable_norm_iff (aestronglyMeasurable_deriv _ _)).mp <|
    h_int.congr_fun (fun t ht ↦ ?_) measurableSet_Ici
  rw [norm_eq_abs, deriv_cpow_const' (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr
    (ne_zero_of_re_pos hs)), map_mul, abs_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht)]

private theorem aux2 (f : ℕ → ℂ) (hf₀ : f 0 = 0) (s : ℂ) (n : ℕ) :
    ∑ k in range (n + 1), LSeries.term f s k = ∑ k ∈ Icc 0 n, ↑k ^ (- s) * f k := by
  rw [← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain hk | rfl := ne_or_eq k 0
  · rw [LSeries.term_of_ne_zero hk, Complex.cpow_neg, mul_comm, div_eq_mul_inv]
  · rw [LSeries.term_zero, hf₀, mul_zero]

private theorem aux3 {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop] fun t : ℝ ↦ t ^ r := by
  refine (Asymptotics.IsBigO.comp_tendsto hbO tendsto_nat_floor_atTop).trans <|
    (Asymptotics.isEquivalent_nat_floor).isBigO.rpow hr ?_
  filter_upwards [eventually_ge_atTop 0] with _ ht using ht

private theorem aux4 {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → 𝕜} {g : ℕ → 𝕜} (r : ℝ) (s : ℂ)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ s.re)
    (hf : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun n ↦ g n * ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (s.re + r) := by
  refine Asymptotics.IsBigO.congr' (hg.mul hf) EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with _ h using by rw [← Real.rpow_add (Nat.cast_pos.mpr h)]

private theorem aux4' {𝕜 : Type*} [RCLike 𝕜]
    {f : ℕ → 𝕜} {g : ℝ → 𝕜} {r : ℝ} (s : ℂ) (hr : 0 ≤ r)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ s.re)
    (hf : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ g t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop] fun t ↦ (t : ℝ) ^ (s.re + r) := by
  refine Asymptotics.IsBigO.congr' (hg.mul (aux3 hr hf)) EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with _ h using by rw [← Real.rpow_add h]

theorem integral_repr (f : ℕ → ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (s : ℂ)
    (hs : r < s.re)
    (hLS : LSeriesSummable f s)
    (hbO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have h_fg : ∀ {n : ℕ}, n ≠ 0 → f n = g n := fun h ↦ by simp only [g, if_neg h]
  have h_g₀ : g 0 = 0 := by simp only [reduceIte, g]
  have h_sum : ∀ n, ∑ k ∈ Icc 0 n, g k = ∑ k ∈ Icc 1 n, f k := by
    intro n
    rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert, h_g₀, zero_add, zero_add,
      sum_congr rfl (fun _ h ↦ by rw [← h_fg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne'])]
    simp only [mem_Icc, not_and, zero_add, nonpos_iff_eq_zero, one_ne_zero, false_implies]
  simp_rw [← h_sum] at hbO
  have h_lim : Tendsto (fun n : ℕ ↦ (n : ℂ) ^ (-s) * ∑ k ∈ Icc 0 n, g k)
      Filter.atTop (nhds 0) := by
    refine Asymptotics.IsBigO.trans_tendsto ?_ <|
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
    simp_rw [Function.comp_def, neg_sub', sub_neg_eq_add]
    refine aux4 r (- s) ?_ hbO
    simp_rw [← abs_natCast]
    refine (Complex.isTheta_cpow_const_rpow (f := fun n : ℕ ↦ (n : ℂ)) ?_).1
    exact fun h ↦ False.elim <| Complex.re_neg_ne_zero_of_re_pos (hr.trans_lt hs) <| h
  have h_int : IntegrableAtFilter (fun x : ℝ ↦ x ^ ((- s - 1).re + r)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by
        rwa [← lt_neg_add_iff_add_lt, ← neg_re, neg_sub, sub_neg_eq_add, add_re, one_re,
          add_neg_cancel_comm])⟩
  rw [LSeries_congr s h_fg, ← integral_mul_left]
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr
    ((LSeriesSummable_congr s h_fg).mp hLS).hasSum.tendsto_sum_nat) ?_
  simp_rw [aux2 _ h_g₀]
  convert tendsto_sum_mul_atTop_eq_sub_integral₀ g h_g₀ ?_ (aux1 (hr.trans_lt hs)) h_lim ?_ h_int
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp_rw [h_sum, Complex.deriv_cpow_const' (zero_lt_one.trans ht).ne'
      (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))]
    ring
  · intro t ht
    exact differentiableAt_id'.cpow_const' (zero_lt_one.trans_le ht).ne'
      (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))
  · refine aux4' (f := g) (s := - s - 1)
      (g := fun t : ℝ ↦ deriv (fun t : ℝ ↦ (t : ℂ) ^ (-s)) t) ?_ ?_ hbO
    · exact hr
    · rw [sub_re, one_re]
      exact isBigO_deriv_cpow_const_atTop (- s)

example (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ⌊t⌋₊ / (t : ℂ) ^ (s + 1) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  rw [integral_repr _ zero_le_one s hs (LSeriesSummable_one_iff.mpr hs)]
  · rw [mul_right_inj' (Complex.ne_zero_of_one_lt_re hs)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp_rw [Pi.one_apply, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one,
      div_eq_mul_inv, ← Complex.cpow_neg, neg_add']
  · simp_rw [Real.rpow_one]
    refine Eventually.isBigO ?_
    filter_upwards with n using by simp

theorem summable_of_abel (f : ℕ → ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (s : ℂ)
    (hs : r < s.re)
    :
    LSeriesSummable f s := by
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have h_fg : ∀ {n : ℕ}, n ≠ 0 → f n = g n := fun h ↦ by simp only [g, if_neg h]
  have h_g₀ : g 0 = 0 := by simp only [g, reduceIte]
  have h_sum : ∀ n, ∑ k ∈ Icc 0 n, ‖g k‖ = ∑ k ∈ Icc 1 n, ‖f k‖ := by
    intro n
    rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert, h_g₀, zero_add, norm_zero, zero_add,
      sum_congr rfl (fun _ h ↦ by rw [← h_fg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne'])]
    simp only [mem_Icc, not_and, zero_add, nonpos_iff_eq_zero, one_ne_zero, false_implies]
  simp_rw [← h_sum] at hbO
  have h_int : IntegrableAtFilter (fun x : ℝ ↦ x ^ ((- s - 1).re + r)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by
        rwa [← lt_neg_add_iff_add_lt, ← neg_re, neg_sub, sub_neg_eq_add, add_re, one_re,
          add_neg_cancel_comm])⟩
  have h_seq : Set.EqOn (deriv fun t : ℝ ↦ t ^ (-s.re))
      (deriv fun t ↦ ‖(fun t : ℝ ↦ (t : ℂ) ^ (-s)) t‖) (Set.Ici 1) := by
    intro t ht
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [eventually_gt_nhds (zero_lt_one.trans_le ht)] with x hx
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx, neg_re]
  rw [LSeriesSummable_congr s h_fg]
  refine Summable.congr_atTop (f₁ := fun n ↦ (n : ℂ) ^ (-s) * (g n)) ?_ ?_
  · refine summable_mul_of_bigO_atTop₀ g ?_ (f := fun t ↦ (t : ℂ) ^ (-s))
      ?_ ?_ ?_ ?_ h_int
    · exact h_g₀
    · intro t ht
      · refine DifferentiableAt.norm ℂ ?_ ?_
        · refine DifferentiableAt.cpow_const' ?_ ?_ ?_
          · exact differentiableAt_id
          · exact (zero_lt_one.trans_le ht).ne'
          · exact (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))
        refine (Complex.cpow_ne_zero ?_).mpr ?_
        · exact (neg_ne_zero.mpr <| Complex.ne_zero_of_re_pos (hr.trans_lt hs))
        · exact_mod_cast (zero_lt_one.trans_le ht).ne'
    · refine IntegrableOn.congr_fun ?_ h_seq measurableSet_Ici
      refine IntegrableOn.congr_fun ?_
        (fun t ht ↦ by
          rw [Real.deriv_rpow_const]
          left
          exact (zero_lt_one.trans_le ht).ne') measurableSet_Ici
      refine Integrable.const_mul (integrableOn_Ici_iff_integrableOn_Ioi.mpr
        ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr ?_)) _
      rw [sub_lt_iff_lt_add, neg_add_cancel, neg_lt_zero]
      exact hr.trans_lt hs
    · have := aux4 r (- r) (f := fun n ↦ ‖g n‖) (g := fun n ↦ ‖(n : ℂ) ^ (-s)‖) ?_ ?_
      · simp_rw [neg_re, ofReal_re, neg_add_cancel, Real.rpow_zero] at this
        exact this
      · refine Eventually.isBigO ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        rw [norm_norm, Complex.norm_natCast_cpow_of_re_ne_zero, neg_re, neg_re, ofReal_re]
        · refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
          · exact_mod_cast hn
          · rw [neg_le_neg_iff]
            exact hs.le
        refine re_neg_ne_zero_of_re_pos ?_
        exact hr.trans_lt hs
      exact hbO
    · refine aux4' _ hr ?_ ?_
      · have : (deriv fun t : ℝ ↦ t ^ (-s.re)) =ᶠ[atTop]
            (deriv fun t ↦ ‖(fun t : ℝ ↦ (t : ℂ) ^ (-s)) t‖) := by
          filter_upwards [eventually_ge_atTop 1] with t ht using h_seq ht
        refine Asymptotics.IsBigO.congr' ?_ this EventuallyEq.rfl
        rw [sub_re, one_re]
        exact isBigO_deriv_rpow_const_atTop (- s.re)
      exact hbO
  · filter_upwards [eventually_ne_atTop 0] with n hn
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, Complex.cpow_neg, mul_comm]

variable (f : ℕ → ℂ) (l : ℂ)
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k : ℂ) / n) atTop (𝓝 l))

include hlim

theorem lemma1 :
    Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
  have lim1 : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / ⌊t⌋₊) atTop (𝓝 l) :=
    Tendsto.comp hlim (tendsto_nat_floor_atTop (α := ℝ))
  have lim2 : Tendsto (fun t : ℝ ↦ ↑(⌊t⌋₊ / t : ℝ)) atTop (𝓝 (1 : ℂ)) := by
    rw [← Complex.ofReal_one]
    rw [tendsto_ofReal_iff]
    exact tendsto_nat_floor_div_atTop
  have lim3 := Tendsto.mul lim1 lim2
  rw [mul_one] at lim3
  refine Tendsto.congr' ?_ lim3
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Complex.ofReal_div, Complex.ofReal_natCast, div_mul_div_cancel₀]
  rw [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
  exact ht

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ < ε * t := by
  rw [Metric.tendsto_nhds] at hlim
  specialize hlim ε hε
  filter_upwards [eventually_gt_atTop 0, hlim] with t ht₁ ht₂
  rwa [← div_lt_iff₀, ← Real.norm_of_nonneg (r := t), ← Complex.norm_real, ← norm_div,
    Complex.norm_real, Real.norm_of_nonneg (r := t), sub_div, mul_div_cancel_right₀]
  · exact_mod_cast ht₁.ne'
  · exact ht₁.le
  · exact ht₁.le
  · exact ht₁
