/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
  # Docs
-/

open Finset Filter MeasureTheory Topology Complex Asymptotics

-- Clear the Asymptotics

section lemmas

theorem aux₁ {f : ℕ → ℂ} {s : ℂ} {n : ℕ} :
    LSeries.term f s n = (n : ℂ) ^ (- s) * (fun n ↦ if n = 0 then 0 else f n) n := by
  cases n with
  | zero => simp only [LSeries.term_zero, Nat.cast_eq_zero, reduceIte, mul_zero]
  | succ n =>
      dsimp only
      rw [LSeries.term_of_ne_zero (by omega), if_neg (by omega), div_eq_mul_inv,
        Complex.cpow_neg, mul_comm]

theorem aux₂ {r : ℝ} (hr : r < -1) :
    IntegrableAtFilter (fun t : ℝ  ↦ t ^ r) atTop :=
  ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr hr⟩

theorem aux₃ {t : ℝ} {c : ℂ} (ht : t ≠ 0) (hc : c ≠ 0) :
    DifferentiableAt ℝ (fun x : ℝ ↦ ‖(fun t ↦ (t : ℂ) ^ c) x‖) t :=
  (differentiableAt_id.cpow_const' ht hc).norm ℝ ((cpow_ne_zero hc).mpr <| ofReal_ne_zero.mpr ht)

theorem aux₄₀ {t : ℝ} {c : ℂ} (ht : 0 < t):
    ‖(t : ℂ) ^ c‖ = t ^ c.re := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos ht]

theorem aux₄₁ {t : ℝ} {c : ℂ} (ht : 0 < t) :
    (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ c‖) t = c.re * t ^ (c.re - 1) := by
  rw [← Real.deriv_rpow_const (Or.inl ht.ne')]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_gt_nhds ht] with x hx
  exact aux₄₀ hx

theorem aux₄₁₁ {c : ℂ} :
    (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ c‖) =ᶠ[atTop] fun t ↦ c.re * t ^ (c.re - 1) := by
  filter_upwards [eventually_gt_atTop 0] with t ht using aux₄₁ ht

theorem aux₄₂ {t : ℝ} {c : ℂ} (ht : t ≠ 0) (hc : c ≠ 0) :
    (deriv fun (t : ℝ) ↦ (t : ℂ) ^ c) t = c * (t : ℂ) ^ (c - 1) :=
  deriv_cpow_const' ht hc

theorem aux₄ {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (deriv fun t : ℝ ↦ ‖(t : ℂ) ^ (- c)‖) (Set.Ici 1) := by
  refine IntegrableOn.congr_fun (Integrable.const_mul ?_ _)
    (fun t ht ↦ (aux₄₁ (zero_lt_one.trans_le ht)).symm) measurableSet_Ici
  exact integrableOn_Ici_iff_integrableOn_Ioi.mpr <|
    (integrableOn_Ioi_rpow_iff zero_lt_one).mpr
      (by rwa [sub_lt_iff_lt_add, neg_add_cancel, neg_re, neg_lt_zero])

theorem aux₅ {R : Type*} [AddCommMonoid R] {f : ℕ → R} {n : ℕ} :
    ∑ k ∈ Icc 0 n, (fun n ↦ if n = 0 then 0 else f n) k =
      ∑ k ∈ Icc 1 n, f k := by
  rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert (mem_Icc.not.mpr (by omega)),
    zero_add, if_pos rfl, zero_add]
  exact Finset.sum_congr rfl
    (fun _ h ↦ by rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne'])

theorem aux₆ {f : ℕ → ℂ} {n : ℕ} :
    ∑ k ∈ Icc 0 n, ‖(fun n ↦ if n = 0 then 0 else f n) k‖ =
      ∑ k ∈ Icc 1 n, ‖f k‖ := by
  simp_rw [apply_ite, norm_zero]
  exact aux₅

theorem aux₇₀ (c : ℂ) :
    (fun t : ℝ ↦ ‖(t : ℂ) ^ c‖) =O[atTop] fun t ↦ t ^ c.re := by
  refine EventuallyEq.isBigO ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [aux₄₀ ht]

theorem aux₇ (c : ℂ) :
    (fun n : ℕ ↦ ‖(n : ℂ) ^ c‖) =O[atTop] fun n ↦ (n : ℝ) ^ c.re :=
  (aux₇₀ c).natCast_atTop

theorem aux₈₀ {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-r)) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop

theorem aux₈ {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    ∀ᶠ (x : ℕ) in atTop, ‖(x : ℝ) ^ (- r)‖ < a :=
  (NormedAddCommGroup.tendsto_nhds_zero.mp (aux₈₀ hr)) _ ha

theorem aux₉ {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {f : ℕ → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc m n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ ∑ k ∈ Icc m ⌊t⌋₊, f k) =O[atTop] fun t : ℝ ↦ t ^ r := by
  refine (hbO.comp_tendsto tendsto_nat_floor_atTop).trans <|
    isEquivalent_nat_floor.isBigO.rpow hr ?_
  filter_upwards [eventually_ge_atTop 0] with _ ht using ht

theorem aux₁₀ {t : ℝ} {c : ℂ} (ht : t ≠ 0) (hc : c ≠ 0) :
    DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ c) t :=
  differentiableAt_id.cpow_const' ht hc

theorem aux₁₁ {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ (- c)) (Set.Ici 1) := by
  refine IntegrableOn.congr_fun ?_ (fun t ht ↦ by
    rw [deriv_cpow_const' (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr <| ne_zero_of_re_pos hc)])
    measurableSet_Ici
  refine integrableOn_Ici_iff_integrableOn_Ioi.mpr <|
    Integrable.const_mul ((integrableOn_Ioi_cpow_iff zero_lt_one).mpr ?_) _
  rwa [sub_re, one_re, sub_lt_iff_lt_add, neg_add_cancel, neg_re, neg_lt_zero]

theorem aux₁₂ {c : ℂ} (hc : c ≠ 0) :
    (fun t ↦ deriv (fun x : ℝ ↦ (x : ℂ) ^ c) t) =O[atTop] fun t ↦ t ^ (c.re - 1) := by
  refine IsBigO.congr_left' (f₁ := fun t : ℝ ↦ c * (t : ℂ) ^ (c - 1)) ?_ ?_
  · refine Asymptotics.IsBigO.const_mul_left ?_ _
    rw [← Asymptotics.isBigO_norm_left]
    refine EventuallyEq.isBigO ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [aux₄₀ ht, sub_re, one_re]
  · filter_upwards [eventually_ne_atTop 0] with t ht
    rw [aux₄₂ ht hc]

theorem aux₁₃ {𝕜 : Type*} [RCLike 𝕜] {f g : ℝ → 𝕜} (a b c : ℝ)
    (hf : f =O[atTop] fun t ↦ (t : ℝ) ^ a)
    (hg : g =O[atTop] fun t ↦ (t : ℝ) ^ b) (h : a + b ≤ c) :
    (f * g) =O[atTop] fun t ↦ (t : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

theorem aux₁₄ {𝕜 : Type*} [RCLike 𝕜] {f g : ℕ → 𝕜} (a b c : ℝ)
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ a)
    (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ b) (h : a + b ≤ c) :
    (f * g) =O[atTop] fun n ↦ (n : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

end lemmas

section summable

variable {f : ℕ → ℂ} {r : ℝ} {s : ℂ}

theorem LSeriesSummable_of_sum_norm_bigO
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : 0 ≤ r) (hs : r < s.re) :
    LSeriesSummable f s := by
  change Summable (fun n ↦ LSeries.term f s n)
  simp_rw [aux₁]
  simp_rw [← aux₆] at hO
  refine summable_mul_of_bigO_atTop₀ (fun n ↦ if n = 0 then 0 else f n)
    (f := fun t ↦ (t : ℂ) ^ (-s)) (g := fun t ↦ t ^ ((- s - 1).re + r)) ?_ ?_ ?_ ?_ ?_ (aux₂ ?_)
  · simp
  · intro t ht
    refine aux₃ ?_ ?_
    · -- t ≠ 0
      exact (zero_lt_one.trans_le ht).ne'
    · -- -s ≠ 0
      exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · refine aux₄ ?_
    exact hr.trans_lt hs
  · have : (-s).re + r ≤ 0 := by
      rw [neg_re, neg_add_nonpos_iff]
      exact hs.le
    convert aux₁₄ ((- s).re) r 0 ?_ ?_ this
    · rw [Real.rpow_zero]
    · exact aux₇ (- s)
    · exact hO
  · refine aux₁₃ ((- s).re - 1) r _ ?_ ?_ ?_
    · exact (EventuallyEq.isBigO aux₄₁₁).of_const_mul_right
    · exact aux₉ hr hO
    · rw [sub_re, one_re]
  · -- (-s - 1).re + r < -1
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]

end summable

section integral_repr

theorem integral_repr (f : ℕ → ℂ)
    {r : ℝ}
    (hr : 0 ≤ r)
    {s : ℂ}
    (hs : r < s.re)
    (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  rw [← integral_mul_left]
  simp_rw [← aux₅] at hO
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hS.hasSum.tendsto_sum_nat) ?_
  simp_rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero _), add_tsub_cancel_right,
    aux₁, ← aux₅, mul_comm]
  have : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  convert tendsto_sum_mul_atTop_eq_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0)
    ?_ ?_ ?_ ?_ ?_ ?_ (aux₂ this)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [deriv_cpow_const']
    · ring
    · exact (zero_lt_one.trans ht).ne'
    · exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · simp
  · intro t ht
    refine aux₁₀ ?_ ?_
    · exact (zero_lt_one.trans_le ht).ne'
    · exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · refine aux₁₁ (hr.trans_lt hs)
  · refine Asymptotics.IsBigO.trans_tendsto ?_ (aux₈₀ (r := s.re -r) ?_)
    · refine aux₁₄ (𝕜 := ℂ) (- s.re) _ _ ?_ hO ?_
      · rw [← Asymptotics.isBigO_norm_left]
        exact aux₇ (- s)
      · rw [neg_sub, neg_add_eq_sub]
    · rwa [sub_pos]
  · refine aux₁₃ (- s.re - 1) r _ ?_ ?_ (by simp only [sub_re, neg_re, one_re, le_refl])
    · exact isBigO_deriv_cpow_const_atTop (-s)
    · exact aux₉ hr hO

end integral_repr

section Riemann

example (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ⌊t⌋₊ / (t : ℂ) ^ (s + 1) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  rw [integral_repr _ zero_le_one hs (LSeriesSummable_one_iff.mpr hs)]
  · rw [mul_right_inj' (Complex.ne_zero_of_one_lt_re hs)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp_rw [Pi.one_apply, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one,
      div_eq_mul_inv, ← Complex.cpow_neg, neg_add']
  · simp_rw [Real.rpow_one]
    refine Eventually.isBigO ?_
    filter_upwards with n using by simp

end Riemann

noncomputable section Residue

variable (f : ℕ → ℂ) {l : ℂ}
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k : ℂ) / n) atTop (𝓝 l))

include hlim in
theorem step1 {ε : ℝ} (hε : ε > 0) :
    ∀ᶠ t : ℝ in atTop, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t‖ < ε * t := by
  have h_lim' : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
    have := (hlim.comp tendsto_nat_floor_atTop).mul <|
      tendsto_ofReal_iff.mpr <| tendsto_nat_floor_div_atTop
    rw [ofReal_one, mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Function.comp_def, ofReal_div, ofReal_natCast, div_mul_div_cancel₀]
    rwa [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
  rw [Metric.tendsto_nhds] at h_lim'
  filter_upwards [eventually_gt_atTop 0, h_lim' ε hε] with t ht₁ ht₂
  rwa [dist_eq_norm, div_sub' _ _ _ (ne_zero_of_re_pos ht₁), norm_div, norm_real,
    Real.norm_of_nonneg ht₁.le, mul_comm, div_lt_iff₀ ht₁] at ht₂

theorem key₁ {s : ℝ} (hs : 1 < s ) : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by rwa [neg_lt_neg_iff]) zero_lt_one, Real.one_rpow, neg_div,
    mul_neg, mul_one_div, neg_div', neg_sub', sub_neg_eq_add, div_self
    (neg_add_eq_zero.not.mpr hs.ne')]

theorem key₂ {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ) = 1 := by
  rw [integral_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) zero_lt_one, ofReal_one, one_cpow,
    neg_div, mul_neg, mul_one_div, neg_div', neg_sub', sub_neg_eq_add, div_self]
  contrapose! hs
  rw [neg_add_eq_zero.mp hs, one_re]

include hlim in
theorem key₃ : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp_rw [Real.rpow_one]
  refine Asymptotics.isBigO_norm_left.mp <| Asymptotics.isBigO_of_div_tendsto_nhds ?_ ‖l‖ ?_
  · filter_upwards [eventually_ne_atTop 0] with _ h using
      fun h' ↦ False.elim <| h (Nat.cast_eq_zero.mp h')
  · simpa only [Function.comp_def, norm_div, norm_natCast] using (tendsto_norm.comp hlim)

theorem key₄ {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ c) (Set.Icc a b) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  exact continuous_ofReal.continuousOn.cpow_const
    (fun x hx ↦ ofReal_mem_slitPlane.mpr (ha.trans_le hx.1))

theorem key₅ {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re):
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (- c)) (Set.Ioi a) :=
  integrableOn_Ioi_cpow_of_lt (by rwa [neg_re, neg_lt_neg_iff]) ha

theorem key₆ {a b : ℝ} {c : ℂ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ c) (Set.Icc a b) := by
  simp_rw [mul_comm]
  exact integrableOn_mul_sum _ ha.le (key₄ ha)

include hlim in
theorem key₇ {a : ℝ} {c : ℂ} (ha : 0 < a) (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (c + 1))) (Set.Ici a) := by
  refine LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^ (- c.re)) ?_ ?_ ?_
  · simp_rw [mul_comm]
    refine locallyIntegrableOn_mul_sum _ ha.le <|
      integrableOn_Ici_iff_integrableOn_Ioi.mpr (key₅ ha ?_)
    rw [add_re, one_re, lt_add_iff_pos_left]
    exact zero_lt_one.trans hc
  · refine aux₁₃ 1 (- (c + 1).re) _ ?_ ?_ ?_
    · exact aux₉ zero_le_one (key₃ f hlim)
    · rw [← Asymptotics.isBigO_norm_left]
      exact aux₇₀ _
    · simp only [add_re, one_re, neg_add_rev, add_neg_cancel_left, le_refl]
  · refine aux₂ ?_
    rwa [neg_lt_neg_iff]

theorem key₈ {T : ℝ} {c : ℂ} (hc : 1 < c.re) :
    ‖∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- c - 1)‖ ≤
      ∫ (t : ℝ) in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-2 : ℂ)‖ := by
  by_cases hT : 1 < T
  · refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · rw [← neg_add']
      exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₆ _ zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₆ _ zero_lt_one).norm
    · have ht' : 0 < t := zero_lt_one.trans ht.1
      rw [norm_mul, norm_mul, aux₄₀ ht', aux₄₀ ht', sub_re, one_re, neg_re, neg_re, re_ofNat]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, norm_zero]

theorem key₉ {T : ℝ} {c : ℂ} (hc :1 < c.re):
    ‖l * ∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- c)‖ ≤
      ‖l‖ * ∫ (t : ℝ) in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖ := by
  by_cases hT : 1 < T
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₄ zero_lt_one).norm
    · exact (integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₄ zero_lt_one).norm
    · have ht' : 0 < t := zero_lt_one.trans ht.1
      rw [aux₄₀ ht', aux₄₀ ht', neg_re, neg_re, one_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (neg_le_neg_iff.mpr hc.le)
  · rw [Set.Ioc_eq_empty hT, setIntegral_empty, setIntegral_empty, mul_zero, norm_zero, mul_zero]

theorem key₁₀ (ε : ℝ) {T : ℝ} {c : ℂ} (hT : 0 < T) (hc : 1 < c.re) :
    IntegrableOn (fun t : ℝ ↦ ‖ε * t‖ * ‖(t : ℂ) ^ (- c - 1)‖) (Set.Ioi T) := by
  simp_rw [← norm_real, ← norm_mul, ofReal_mul, mul_assoc]
  refine (((key₅ hT hc).congr ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)).const_mul _).norm
  filter_upwards with t ht
  rw [cpow_sub, cpow_one, mul_div_cancel₀]
  all_goals exact_mod_cast (hT.trans ht).ne'

theorem key₁₁ {g : ℕ → ℂ} {c : ℂ} :
     Measurable (fun t : ℝ ↦ ‖(∑ k in Icc 1 ⌊t⌋₊, g k) - c * t‖) :=
  (((by exact fun _ _ ↦ trivial : Measurable fun n : ℕ ↦ ∑ k ∈ Icc 1 n, g k).comp'
    Nat.measurable_floor).sub (by fun_prop)).norm

variable (hfS : ∀ s : ℝ, s > 1 → LSeriesSummable f s)

include hlim hfS in
theorem key_step {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop).mp <| step1 f hlim hε
  let T := max 1 T₀
  have hT : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- 2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖
  refine ⟨C₁ + C₂, ?_, ?_⟩
  · exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) <|
      mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  · intro s hs
    have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
    have hT' : ∀ t ∈ Set.Ioi T,
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ * ‖(t : ℂ) ^ (- (s : ℂ) - 1)‖ ≤ ‖ε * t‖ *
          ‖(t : ℂ) ^ (- (s : ℂ) - 1)‖ := sorry
    let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)
    let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ)
    calc
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ))
              - l * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ))‖ := ?_
      _ = ‖(s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) +
              (∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ))
                - l * ((∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ))
                  + (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))))‖ := ?_
      _ = ‖(s - 1) * s * C₁s  - (s - 1) * s * C₂s +
            (s - 1) * s *
              ((∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ)))‖ := by congr; ring
      _ ≤ (s - 1) * s * ‖C₁s‖ + (s - 1) * s * ‖C₂s‖ +
            (s - 1) * s *
              ‖(∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) -
                l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))‖ := ?_
      _ ≤ (s - 1) * s * C₁ + (s - 1) * s * C₂ +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ) - l * (t : ℂ) ^ (- s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ‖∫ (t : ℝ) in Set.Ioi T,
                ((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t) * (t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s *
              ∫ (t : ℝ) in Set.Ioi T,
                ‖((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t)‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ‖ε * t‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ∫ (t : ℝ) in Set.Ioi 1, ‖ε * t‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
      _ ≤ (s - 1) * s * (C₁ + C₂) +
            (s - 1) * s * ε * ∫ (t : ℝ) in Set.Ioi 1, ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
      _ = (s - 1) * s * (C₁ + C₂) +
            s * ε * (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) := ?_
      _ = (s - 1) * s * (C₁ + C₂) + s * ε := ?_
    · rw [integral_repr _ zero_le_one (by rwa [ofReal_re]) (hfS _ hs), mul_sub, ← mul_assoc _ l,
        mul_rotate _ _ l, mul_assoc, mul_assoc, key₂ (by rwa [ofReal_re]), mul_one, mul_comm l]
      exact key₃ f hlim
    · rw [← Set.Ioc_union_Ioi_eq_Ioi (le_max_left 1 T₀)]
      rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi, setIntegral_union
        (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi]
      · exact integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₄ zero_lt_one
      · exact key₅ hT (by rwa [ofReal_re])
      · exact integrableOn_Icc_iff_integrableOn_Ioc.mp <| key₆ f zero_lt_one
      · rw [← neg_add']
        refine integrableOn_Ici_iff_integrableOn_Ioi.mp <| key₇ f hlim hT ?_
        rwa [ofReal_re]
    · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
      rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s),
        show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
          ofReal_one], Complex.norm_real, Real.norm_of_nonneg hs']
    · refine add_le_add (add_le_add ( mul_le_mul_of_nonneg_left ?_ hs')
        (mul_le_mul_of_nonneg_left ?_ hs')) ?_
      · exact key₈ _ (by rwa [ofReal_re])
      · exact key₉ (by rwa [ofReal_re])
      · rw [integral_sub, integral_mul_left]
        · rw [← neg_add']
          exact integrableOn_Ici_iff_integrableOn_Ioi.mp <| key₇ f hlim hT (by rwa [ofReal_re])
        · exact Integrable.const_mul (key₅ hT (by rwa [ofReal_re])) _
    · rw [mul_add]
      congr 3
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [sub_mul, cpow_sub, cpow_one, mul_assoc, mul_div_cancel₀]
      all_goals exact_mod_cast (hT.trans ht).ne'
    · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
      exact le_of_le_of_eq (norm_integral_le_integral_norm _) (by simp_rw [norm_mul])
    · refine add_le_add_left (mul_le_mul_of_nonneg_left
        (setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_) hs') _
      · refine Integrable.mono (key₁₀ ε hT (by rwa [ofReal_re])) ?_
          ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
        · refine Measurable.aestronglyMeasurable ?_
          exact key₁₁.mul (by fun_prop)
        · filter_upwards with t ht
          rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          exact hT' t ht
      · refine key₁₀ ε hT (by rwa [ofReal_re])
      · exact hT'
    · gcongr
      refine setIntegral_mono_set ?_ ?_ ?_
      · refine key₁₀ _ ?_ ?_
        exact zero_lt_one
        

        sorry
      · sorry
      · sorry
    · sorry
    · sorry
    · sorry







#exit







end Residue

variable (f : ℕ → ℂ) {l : ℂ}
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, f k : ℂ) / n) atTop (𝓝 l))

include hlim

theorem lemma0 {ε : ℝ} (hε : ε > 0) :
    ∀ᶠ t : ℝ in atTop, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t‖ < ε * t := by
  have h_lim' : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
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
  rw [Metric.tendsto_nhds] at h_lim'
  specialize h_lim' ε hε
  filter_upwards [eventually_gt_atTop 0, h_lim'] with t ht₁ ht₂
  rwa [← div_lt_iff₀, ← Real.norm_of_nonneg (r := t), ← Complex.norm_real, ← norm_div,
    Complex.norm_real, Real.norm_of_nonneg (r := t), sub_div, mul_div_cancel_right₀]
  · exact_mod_cast ht₁.ne'
  · exact ht₁.le
  · exact ht₁.le
  · exact ht₁

theorem lemma1 :
    (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) := by
  rw [← Asymptotics.isBigO_norm_left]
  refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ ‖l‖ ?_
  · filter_upwards [eventually_ne_atTop 0] with _ h using
      fun h' ↦ False.elim <| h (Nat.cast_eq_zero.mp h')
  · simpa only [Function.comp_def, norm_div, norm_natCast] using (tendsto_norm.comp hlim)

theorem lemma2 :
    (fun t : ℝ ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, f k) =O[atTop] fun t : ℝ ↦ t := by
  refine Asymptotics.IsBigO.congr_right (aux3 (f := f) (m := 1) zero_le_one ?_) ?_
  · simp_rw [Real.rpow_one]
    exact lemma1 f l hlim
  · intro _
    rw [Real.rpow_one]

variable (hfS : ∀ s : ℝ, s > 1 → LSeriesSummable f s)

include hfS

private theorem key_lemma {ε : ℝ} (hε : ε > 0) :
    ∃ C ≥ 0, ∀ s : ℝ, 1 < s → ‖(s - 1) * LSeries f s - l * s‖ ≤ (s - 1) * s * C + s * ε := by
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop).mp <| lemma0 f l hlim hε
  let T := max 1 T₀
  have hT : ∀ t ≥ T, ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * t‖ ≤ ε * t :=
    fun _ h ↦ (hT₀  _ <| (le_max_right _ _).trans h).le
  let C₁ := ∫ t in Set.Ioc 1 T, ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- 2 : ℂ)‖
  let C₂ := ‖l‖ * ∫ t in Set.Ioc 1 T, ‖(t : ℂ) ^ (- 1 : ℂ)‖
  use C₁ + C₂
  refine ⟨?_, ?_⟩
  · refine add_nonneg ?_ ?_
    · refine integral_nonneg ?_
      intro _
      exact norm_nonneg _
    · refine mul_nonneg (norm_nonneg _) (integral_nonneg ?_)
      intro _
      exact norm_nonneg _
  intro s hs
  have hs' : 0 ≤ (s - 1) * s := mul_nonneg (sub_nonneg.mpr hs.le) (zero_le_one.trans hs.le)
  let C₁s := ∫ t in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)
  let C₂s := l * ∫ t in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ)
  have h_intOn₁ : ∀ ⦃a b : ℝ⦄ ⦃c : ℂ⦄, 0 < a →
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ c) (Set.Icc a b) :=
    fun _ _ _ h ↦ (continuous_ofReal.continuousOn.cpow_const
        fun x hx ↦ ofReal_mem_slitPlane.mpr (h.trans_le hx.1)).integrableOn_compact isCompact_Icc
  have h_intOn₂ :  ∀ ⦃a b : ℝ⦄ ⦃c : ℂ⦄, 0 < a →
      IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ c) (Set.Icc a b) := by
    intro _ _ _ h
    simp_rw [mul_comm]
    refine integrableOn_mul_sum _ h.le ?_
    apply h_intOn₁ h
  have h_le : ∀ x ∈ Set.Ioi T,
      ‖∑ k ∈ Icc 1 ⌊x⌋₊, f k - l * x‖ * ‖(x : ℂ) ^ (- (s : ℂ) - 1)‖ ≤
        ‖ε * x‖ * ‖(x : ℂ) ^ (- (s : ℂ) - 1)‖ := by
    intro t ht
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_of_nonneg]
    · exact hT _ ht.le
    · refine mul_nonneg ?_ ?_
      · exact hε.le
      · exact zero_le_one.trans ((le_max_left 1 T₀).trans ht.le)
  have h_intOn₃ : IntegrableOn (fun t : ℝ ↦ ‖ε * t‖ * ‖(t : ℂ) ^ (- (s : ℂ) - 1)‖)
      (Set.Ioi T) := by
    refine IntegrableOn.congr_fun (f := fun t : ℝ ↦ ‖ε‖ * ‖(t : ℂ) ^ (- s : ℂ)‖) ?_ ?_ ?_
    · refine Integrable.const_mul ?_ _
      refine Integrable.norm ?_
      rw [← IntegrableOn, integrableOn_Ioi_cpow_iff]
      · rwa [neg_re, ofReal_re, neg_lt_neg_iff]
      · exact zero_lt_one.trans_le (le_max_left 1 T₀)
    · intro t ht
      dsimp only
      rw [norm_mul, ← Complex.norm_real t, mul_assoc, ← norm_mul, cpow_sub, cpow_one,
        mul_div_cancel₀]
      · exact ofReal_ne_zero.mpr <| (zero_lt_one.trans ((le_max_left 1 T₀).trans_lt ht)).ne'
      · exact ofReal_ne_zero.mpr <| (zero_lt_one.trans ((le_max_left 1 T₀).trans_lt ht)).ne'
    · exact measurableSet_Ioi
  have h_intOn₄ : IntegrableOn (fun t : ℝ ↦ ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k - l * ↑t‖ *
      ‖(t : ℂ) ^ (- (s : ℂ) - 1)‖) (Set.Ioi T) := by
    refine Integrable.mono h_intOn₃ ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.mul ?_ ?_
      · refine Measurable.norm ?_
        refine Measurable.sub ?_ ?_
        · refine Measurable.comp' (β := ℕ) -- Lean needs this hint for unification
            (by exact fun _ _ ↦ trivial : Measurable fun n : ℕ ↦ ∑ k ∈ Icc 1 n, f k)
            Nat.measurable_floor
        · fun_prop
      · fun_prop
    · rw [ae_restrict_iff']
      filter_upwards with t ht
      rw [norm_mul, norm_mul, norm_norm, norm_norm, norm_norm]
      exact h_le t ht
      exact measurableSet_Ioi
  have h_intOn₅ : IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- (s : ℂ) - 1))
      (Set.Ioi T) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    refine LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun t ↦ t ^ (-s)) ?_ ?_ ?_
    · simp_rw [mul_comm]
      refine locallyIntegrableOn_mul_sum _ ?_ ?_
      · exact zero_le_one.trans (le_max_left 1 T₀)
      · rw [integrableOn_Ici_iff_integrableOn_Ioi]
        rw [integrableOn_Ioi_cpow_iff]
        · rw [sub_re, neg_re, ofReal_re, one_re]
          rw [lt_neg_iff_add_neg, sub_add_cancel, neg_lt_zero]
          exact zero_lt_one.trans hs
        · exact zero_lt_one.trans_le (le_max_left 1 T₀)
    · have a₁ := lemma2 f l hlim
      have a₂ := Asymptotics.IsBigO.norm_right <|
        Asymptotics.isBigO_refl (fun t : ℝ ↦ (t : ℂ) ^ (- (s : ℂ) - 1)) atTop
      have := a₁.mul a₂
      refine Asymptotics.IsBigO.congr' this ?_ ?_
      · exact EventuallyEq.rfl
      · filter_upwards [eventually_ge_atTop 0] with t ht
        rw [show (t : ℂ) ^ (- (s : ℂ) - 1) = (t ^ (- s - 1) : ℝ) by
          rw [ofReal_cpow, ofReal_sub, ofReal_neg, ofReal_one]
          exact ht]
        rw [norm_real, Real.norm_of_nonneg, ← Real.rpow_one_add', add_sub_cancel]
        · exact ht
        · rw [add_sub_cancel, neg_ne_zero]
          exact (zero_lt_one.trans hs).ne'
        · refine Real.rpow_nonneg ?_ _
          exact ht
    · refine ⟨Set.Ioi T, Ioi_mem_atTop T, ?_⟩
      rw [integrableOn_Ioi_rpow_iff]
      · rwa [neg_lt_neg_iff]
      · exact zero_lt_one.trans_le (le_max_left 1 T₀)
  have hC₁ : ‖C₁s‖ ≤ C₁ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · refine Integrable.norm ?_
      rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioc]
      apply h_intOn₂ zero_lt_one
    · refine Integrable.norm ?_
      rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioc]
      apply h_intOn₂ zero_lt_one
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [show (t : ℂ) ^ (- 2 : ℂ) = (t ^ (- 2 : ℝ) : ℝ) by
      rw [ofReal_cpow, ofReal_neg, ofReal_ofNat]
      exact zero_le_one.trans ht.1.le]
    rw [show (t : ℂ) ^ (- (s : ℂ) - 1) = (t ^ (- s - 1) : ℝ) by
      rw [ofReal_cpow, ofReal_sub, ofReal_neg, ofReal_one]
      exact zero_le_one.trans ht.1.le]
    rw [norm_real, norm_real, Real.norm_of_nonneg, Real.norm_of_nonneg]
    apply Real.rpow_le_rpow_of_exponent_le ?_ ?_
    exact ht.1.le
    · rw [sub_le_iff_le_add]
      rw [show - (2 : ℝ) + 1 = -1 by norm_num, neg_le_neg_iff]
      exact hs.le
    · refine Real.rpow_nonneg ?_ _
      exact zero_le_one.trans ht.1.le
    · refine Real.rpow_nonneg ?_ _
      exact zero_le_one.trans ht.1.le
  have hC₂ : ‖C₂s‖ ≤ C₂ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht ↦ ?_
    · refine Integrable.norm ?_
      rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioc]
      exact h_intOn₁ zero_lt_one
    · refine Integrable.norm ?_
      rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioc]
      exact h_intOn₁ zero_lt_one
    · rw [show (t : ℂ) ^ (- 1 : ℂ) = (t ^ (- 1 : ℝ) : ℝ) by
        rw [ofReal_cpow, ofReal_neg, ofReal_one]
        exact zero_le_one.trans ht.1.le]
      rw [show (t : ℂ) ^ (- (s : ℂ)) = (t ^ (- s) : ℝ) by
        rw [ofReal_cpow, ofReal_neg]
        exact zero_le_one.trans ht.1.le]
      rw [norm_real, norm_real, Real.norm_of_nonneg, Real.norm_of_nonneg]
      apply Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact ht.1.le
      · rw [neg_le_neg_iff]
        exact hs.le
      · refine Real.rpow_nonneg ?_ _
        exact zero_le_one.trans ht.1.le
      · refine Real.rpow_nonneg ?_ _
        exact zero_le_one.trans ht.1.le
  have h_int : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) = 1 := by
    rw [integral_Ioi_rpow_of_lt _ zero_lt_one, Real.one_rpow, neg_div, mul_neg, mul_one_div,
      neg_div', neg_sub', sub_neg_eq_add, div_self]
    · exact neg_add_eq_zero.not.mpr hs.ne'
    · exact neg_lt_neg_iff.mpr hs
  have h_int' : (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ) = 1 := by
    rw [integral_Ioi_cpow_of_lt _ zero_lt_one, Complex.ofReal_one, Complex.one_cpow, neg_div,
      mul_neg, mul_one_div, neg_div', neg_sub', sub_neg_eq_add, div_self]
    · exact neg_add_eq_zero.not.mpr <| ofReal_ne_one.mpr hs.ne'
    · rwa [neg_re, ofReal_re, neg_lt_neg_iff]
  have h_Iio₁ : Set.Ioi 1 = Set.Ioc 1 T ∪ Set.Ioi T := by
    rw [Set.Ioc_union_Ioi_eq_Ioi (le_max_left 1 T₀)]
  have h_Iio₂ : Disjoint (Set.Ioc 1 T) (Set.Ioi T) := Set.Ioc_disjoint_Ioi le_rfl
  calc
    _ = ‖(s - 1) * s *
          ((∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ))
            - l * ∫ (t : ℝ) in Set.Ioi 1, (t : ℂ) ^ (- s : ℂ))‖ := ?_
    _ = ‖(s - 1) * s *
          ((∫ (t : ℝ) in Set.Ioc 1 T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) +
          (∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ))
            - l * ((∫ (t : ℝ) in Set.Ioc 1 T, (t : ℂ) ^ (- s : ℂ))
            + (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))))‖ := ?_
    _ = ‖(s - 1) * s * C₁s  - (s - 1) * s * C₂s +
          (s - 1) * s *
            ((∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) -
              l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ)))‖ := ?_
    _ ≤ (s - 1) * s * ‖C₁s‖ + (s - 1) * s * ‖C₂s‖ +
          (s - 1) * s *
            ‖(∫ (t : ℝ) in Set.Ioi T, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ)) -
              l * (∫ (t : ℝ) in Set.Ioi T, (t : ℂ) ^ (- s : ℂ))‖ := ?_
    _ ≤ (s - 1) * s * C₁ + (s - 1) * s * C₂ +
          (s - 1) * s *
            ‖∫ (t : ℝ) in Set.Ioi T,
              (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (- s - 1 : ℂ) - l * (t : ℂ) ^ (- s : ℂ)‖ := ?_
    _ = (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s *
            ‖∫ (t : ℝ) in Set.Ioi T,
              ((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t) * (t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
    _ ≤ (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s *
            ∫ (t : ℝ) in Set.Ioi T,
              ‖((∑ k ∈ Icc 1 ⌊t⌋₊, f k) - l * t)‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
    _ ≤ (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ‖ε * t‖ * ‖(t : ℂ) ^ (- s - 1 : ℂ)‖ := ?_
    _ = (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s * ∫ (t : ℝ) in Set.Ioi T, ε * ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
    _ ≤ (s - 1) * s * (C₁ + C₂) +
          (s - 1) * s * ε * ∫ (t : ℝ) in Set.Ioi 1, ‖(t : ℂ) ^ (- s : ℂ)‖ := ?_
    _ = (s - 1) * s * (C₁ + C₂) +
          s * ε * (s - 1) * ∫ (t : ℝ) in Set.Ioi 1, t ^ (- s) := ?_
    _ = (s - 1) * s * (C₁ + C₂) + s * ε := ?_
  · rw [integral_repr _ zero_le_one, mul_sub, ← mul_assoc _ l, mul_rotate _ _ l,
      mul_assoc, mul_assoc, h_int', mul_one, mul_comm l]
    · rwa [ofReal_re]
    · exact hfS _ hs
    · simp_rw [Real.rpow_one]
      exact lemma1 f l hlim
  · rw [h_Iio₁, setIntegral_union h_Iio₂ measurableSet_Ioi, setIntegral_union h_Iio₂
      measurableSet_Ioi]
    · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
      apply h_intOn₁ zero_lt_one
    · rw [integrableOn_Ioi_cpow_iff]
      · rwa [neg_re, ofReal_re, neg_lt_neg_iff]
      · exact zero_lt_one.trans_le (le_max_left 1 T₀)
    · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
      apply h_intOn₂ zero_lt_one
    · exact h_intOn₅
  · congr 1
    ring
  · refine le_trans (norm_add_le _ _) <| le_trans (add_le_add_right (norm_sub_le _ _) _) ?_
    rw [norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s), norm_mul (((s : ℂ) - 1) * s)]
    rw [show (((s : ℂ) - 1) * s)  = ((s - 1) * s : ℝ) by rw [ofReal_mul, ofReal_sub,
      ofReal_one], Complex.norm_real, Real.norm_of_nonneg hs']
  · refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hC₁ hs'
    · exact mul_le_mul_of_nonneg_left hC₂ hs'
    · rw [integral_sub, integral_mul_left]
      · exact h_intOn₅
      · refine Integrable.const_mul ?_ _
        rw [← IntegrableOn, integrableOn_Ioi_cpow_iff]
        · rwa [neg_re, ofReal_re, neg_lt_neg_iff]
        · exact zero_lt_one.trans_le (le_max_left 1 T₀)
  · rw [mul_add]
    congr 3
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| (zero_lt_one.trans ((le_max_left 1 T₀).trans_lt ht)).ne'
    rw [sub_mul, Complex.cpow_sub _ _ this, Complex.cpow_one, mul_assoc, mul_div_cancel₀ _ this]
  · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
    exact le_of_le_of_eq (norm_integral_le_integral_norm _) (by simp_rw [norm_mul])
  · refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ hs') _
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
    · exact h_intOn₄
    · exact h_intOn₃
    · exact h_le
  · congr 2
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| (zero_lt_one.trans ((le_max_left 1 T₀).trans_lt ht)).ne'
    rw [norm_mul, Real.norm_of_nonneg hε.le, ← Complex.norm_real, mul_assoc, ← norm_mul,
      Complex.cpow_sub _ _ this, Complex.cpow_one, mul_div_cancel₀ _ this]
  · rw [integral_mul_left, ← mul_assoc]
    refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hs' hε.le)) _
    refine setIntegral_mono_set ?_ ?_ ?_
    · refine Integrable.norm ?_
      rw [← IntegrableOn, integrableOn_Ioi_cpow_iff]
      · rwa [neg_re, ofReal_re, neg_lt_neg_iff]
      · exact zero_lt_one
    · filter_upwards with _ using norm_nonneg _
    · exact HasSubset.Subset.eventuallyLE <| Set.Ioi_subset_Ioi (le_max_left 1 T₀)
  · congr 2
    · ring
    · refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (zero_le_one.trans ht.le), Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.le) _)]
  · rw [mul_assoc _ (s - 1), h_int, mul_one]

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨C, hC₁, hC₂⟩ := key_lemma f hlim hfS hε6
  have lim1 : Tendsto (fun s ↦ (s - 1) * s * C) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun s ↦ (s - 1) * s * C) 1 := by fun_prop
    have := this.tendsto
    rwa [sub_self, zero_mul, zero_mul] at this
  have lim2 : Tendsto (fun s : ℝ ↦ s * l) (𝓝[>] 1) (𝓝 l) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : ContinuousAt (fun s : ℝ ↦ s * l) 1 := by fun_prop
    have := this.tendsto
    rwa [Complex.ofReal_one, one_mul] at this
  rw [Metric.tendsto_nhdsWithin_nhds] at lim1 lim2
  obtain ⟨δ₁, _, hδ₁⟩ := lim1 _ hε3
  obtain ⟨δ₂, _, hδ₂⟩ := lim2 _ hε3
  use min 1 (min δ₁ δ₂)
  refine ⟨by positivity, ?_⟩
  intro s hs₁ hs₂
  specialize hC₂ s hs₁
  specialize hδ₁ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_left _ _)
  specialize hδ₂ hs₁ <| hs₂.trans_le <| (min_le_right _ _).trans (min_le_right _ _)
  rw [dist_eq_norm] at hδ₁ hδ₂ hs₂ ⊢
  rw [sub_zero, Real.norm_of_nonneg (mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hs₁.le) (zero_lt_one.trans hs₁).le) hC₁)] at hδ₁
  calc
    _ ≤ ‖(s - 1) * LSeries f s - l * s‖ + ‖l * s - l‖ := ?_
    _ < (s - 1) * s * C + s * (ε / 6) + (ε / 3) := ?_
    _ < (ε / 3) + (ε / 3) + (ε / 3) := ?_
    _ = ε := ?_
  · exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  · refine add_lt_add_of_le_of_lt hC₂ ?_
    rwa [mul_comm]
  · refine (add_lt_add_iff_right _).mpr ?_
    refine add_lt_add ?_ ?_
    · exact hδ₁
    · have : s < 2 := by
        have := hs₂.trans_le (min_le_left _ _)
        rw [Real.norm_eq_abs, abs_lt, sub_lt_iff_lt_add', one_add_one_eq_two] at this
        exact this.2
      have := (mul_lt_mul_right hε6).mpr this
      rwa [show 2 * (ε / 6) = ε / 3 by ring] at this
  · exact add_thirds ε

end

theorem final_real (f : ℕ → ℝ) {l : ℝ}
    (hf : Tendsto (fun n ↦ (∑ k ∈ Icc 1 n, f k) / (n : ℝ)) atTop (𝓝 l))
    (hf' : ∀ n, 0 ≤ f n) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ f n) s) (𝓝[>] 1) (𝓝 l) := by
  refine final (fun n ↦ f n) l ?_ ?_
  · refine hf.ofReal.congr ?_
    intro _
    simp only [ofReal_div, ofReal_sum, ofReal_natCast]
  · intro s hs
    refine summable_of_abel _ zero_le_one ?_ s ?_
    · have := hf.ofReal
      simp at this
      have := Asymptotics.IsBigO.norm_left (lemma1 (fun n ↦ f n) l this)
      simp_rw [Real.rpow_one]
      refine Asymptotics.IsBigO.congr_left this fun _ ↦ ?_
      simp_rw [← ofReal_sum, norm_real, Real.norm_of_nonneg (hf' _)]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ hf' _)]
    · rwa [ofReal_re, ← gt_iff_lt]
