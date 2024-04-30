/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ZetaFunction

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.
-/

noncomputable section

open ModularForm EisensteinSeries UpperHalfPlane Set Filter Function Complex Manifold Matrix

open scoped Topology BigOperators Nat Classical MatrixGroups

namespace EisensteinSeries


lemma UBOUND (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ):
  Complex.abs ((((eisensteinSeries a k))) z) ≤ ∑' (x : Fin 2 → ℤ),
    Complex.abs (eisSummand k x z) := by
sorry
/-  apply le_trans (abs_tsum' ?_)
  simp_rw [feise, eise]
  have := Equiv.tsum_eq prod_fun_equiv.symm (fun x : ℤ × ℤ => (AbsEise k z x))
  rw [←this]

  have Ht := tsum_subtype_le (fun x : (Fin 2 → ℤ)  => (AbsEise k z (prod_fun_equiv.symm x)))
    (lvl_N_congr' N a b) ?_ ?_
  simp_rw [AbsEise] at *
  simp at *
  apply le_trans Ht
  rfl
  intro v
  simp_rw [AbsEise]
  simp

  apply zpow_nonneg (Complex.abs.nonneg _)
  have := real_eise_is_summable k z hk
  rw [←Equiv.summable_iff prod_fun_equiv.symm] at this
  exact this
  rw [←summable_iff_abs_summable]
  apply summable_Eisenstein_N_tsum' k hk
  -/

theorem upp_half_translation_N (z : ℍ) (N : ℤ) (hn : 0  < N) :
    ∃ n : ℤ, ((((ModularGroup.T^N)^n))) • z ∈ verticalStrip N z.1.2 :=
  by
  let n := Int.floor (z.1.1/N)
  use-n
  have hpow : (ModularGroup.T ^ N) ^ (-n) = (ModularGroup.T) ^ (-(N: ℤ)*n) := by
    simp
    norm_cast
    rw [←zpow_mul]
  rw [hpow]
  have := modular_T_zpow_smul z (-N*n)
  simp_rw [this]
  sorry
  /-
  simp only [Int.cast_neg,  abs_ofReal, ge_iff_le]
  constructor
  have HT: (-(N : ℤ)*(n : ℝ) +ᵥ z).1.re= -N *Int.floor (z.1.1/N) + z.re := by rfl
  norm_cast at *
  rw [HT]
  simp
  rw [add_comm]
  have hnn :  (0 : ℝ)  < (N : ℝ) := by norm_cast at *
  have h0 := Int.sub_floor_div_mul_lt (z.1.1 : ℝ) hnn
  simp_rw [UpperHalfPlane.re] at *
  have h1 := Int.sub_floor_div_mul_nonneg (z.1.1 : ℝ) hnn
  have h2 : z.1.1 +-(N*n)=  z.1.1 - n*N := by ring
  simp only [uhc] at *
  rw [h2]
  rw [abs_eq_self.2 h1]
  apply h0.le
  have : (-N*(n : ℝ) +ᵥ z).1.im = z.im := by
    have := vadd_im (-N*(n : ℝ)) z
    rw [← this]
    congr
  simp at *
  rw [this]
  apply le_abs_self
  -/

theorem lvl_N_periodic (N : ℕ) (k : ℤ) (f : SlashInvariantForm (Gamma N) k) :
    ∀ (z : ℍ) (n : ℤ), f (((ModularGroup.T^N)^n) • z) = f z :=
  by
  /-
  have h := SlashInvariantForm.slash_action_eqn' k (Gamma N) f
  intro z n
  simp only [Subgroup.top_toSubmonoid, subgroup_to_sl_moeb, Subgroup.coe_top, Subtype.forall,
    Subgroup.mem_top, forall_true_left] at h
  have Hn :=  (T_pow_N_mem_Gamma' N n)
  simp only [zpow_coe_nat, Int.natAbs_ofNat] at Hn
  have H:= h ((ModularGroup.T^N)^n) Hn z
  rw [H]
  have : ((ModularGroup.T^N)^n)  = (ModularGroup.T^((N : ℤ)*n)) := by
      rw [zpow_mul]
      simp
  simp_rw [this]
  have hh := ModularGroup.coe_T_zpow (N*n)
  rw [slcoe (ModularGroup.T^(N*n)) 1 0, slcoe (ModularGroup.T^(N*n)) 1 1, hh]
  ring_nf
  simp
  -/
  sorry

lemma verticalStrip_mem_le (A B B': ℝ) (hbb : B ≤ B') :
  verticalStrip A B' ⊆ verticalStrip A B := by
  simp_rw [verticalStrip]
  simp only [setOf_subset_setOf, and_imp]
  intro z ha hb
  simp only [ha, true_and]
  apply le_trans hbb hb


theorem Eisenstein_series_is_bounded2 (N : ℕ+) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[(k : ℤ)] A) := by
    simp_rw [UpperHalfPlane.bounded_mem, eisensteinSeries_SIF] at *
    let M' := ∑'(x : Fin 2 → ℤ),
    (1 / r (⟨⟨N, 2⟩, by simp⟩) ^ k) * ((max (x 0).natAbs (x 1).natAbs : ℝ) ^ k)⁻¹
    use M'
    use 2
    intro z hz
    obtain ⟨n, hn⟩ := (upp_half_translation_N z N (by simp))
    rw [eisensteinSeries_slash_apply]
    have := lvl_N_periodic N k (eisensteinSeries_SIF (a ᵥ* A) k) z n
    have h1 :
        (eisensteinSeries_SIF (a ᵥ* ↑((SpecialLinearGroup.map (Int.castRingHom (ZMod ↑N))) A)) k) z =
        eisensteinSeries (a ᵥ* ↑((SpecialLinearGroup.map (Int.castRingHom (ZMod ↑N))) A)) k z := by
        rfl
    rw [← h1, ← this]
    apply le_trans (UBOUND N _ _ hk ((ModularGroup.T ^ (N : ℕ)) ^ n • z))
    let Z := ((ModularGroup.T ^ (N : ℕ)) ^ n) • z
    have hZ : Z ∈ verticalStrip (N : ℕ) 2 := by
      have := verticalStrip_mem_le (N : ℕ) 2 z.im hz
      apply this
      convert hn
      simp only [zpow_natCast]
    apply tsum_le_tsum
    intro x
    simp
    have hk0 : 0 ≤ k := by linarith
    lift k to ℕ using hk0
    have := eis_is_bounded_on_box k (max (x 0).natAbs (x 1).natAbs) Z x (by simp only [Int.mem_box])
    rw [eisSummand]
    simp
    simp only [Fin.isValue, ModularGroup.sl_moeb, map_pow, _root_.map_mul,
      abs_ofReal, abs_natCast, Nat.cast_max, _root_.mul_inv_rev, Z] at this
    apply le_trans this
    rw [mul_comm]
    gcongr
    · apply pow_pos (r_pos _)
    · apply (r_pos _).le
    · apply r_lower_bound_on_strip (A := N) (B := 2) (z:= ⟨Z, hZ⟩)
    apply (summable_upper_bound hk Z).of_nonneg_of_le
    · intro b
      apply (Complex.abs.nonneg _)
    · intro b
      have hk0 : 0 ≤ k := by linarith
      lift k to ℕ using hk0
      have := eis_is_bounded_on_box k (max (b 0).natAbs (b 1).natAbs) Z b (by simp only [Int.mem_box])
      rw [eisSummand]
      simp [Z]
      simp at this
      conv =>
        enter [2]
        rw [mul_comm]
      exact this
    · apply summable_upper_bound hk


    --exact AbsEisenstein_bound_unifomly_on_stip ( k) hk N 2 (by linarith) ⟨Z, hZ⟩
