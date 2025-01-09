/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Temperate growth
-/

open scoped ContDiff FourierTransform

namespace Function

section PeriodicUtil

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- If a function is is periodic, then its derivative is periodic. -/
theorem Periodic.fderiv {f : E → F} {c : E} (hf : Periodic f c) : Periodic (fderiv 𝕜 f) c := by
  intro x
  rw [← fderiv_comp_add_right, hf.funext]

variable (𝕜) in
/-- If a function is is periodic, then all of its derivatives are periodic. -/
theorem Periodic.iteratedFDeriv (n : ℕ) {f : E → F} {c : E} (hf : Periodic f c) :
    Periodic (iteratedFDeriv 𝕜 n f) c := by
  intro x
  rw [← iteratedFDeriv_comp_add_right, hf.funext]

variable {α β : Type*}
  [LinearOrderedAddCommGroup α] [Archimedean α] [TopologicalSpace α] [CompactIccSpace α]
  [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]

theorem Periodic.bddAbove_range_of_continuous [Nonempty β] {f : α → β} {c : α}
    (hf : Periodic f c) (hc : c ≠ 0) (hf_cont : Continuous f) :
    BddAbove (Set.range f) := by
  rw [← hf.image_uIcc hc 0]
  exact IsCompact.bddAbove_image isCompact_uIcc hf_cont.continuousOn

/-- Continuous periodic functions on an infinite, ordered set are bounded. -/
theorem Periodic.exists_bound_of_continuous {f : α → F} {c : α}
    (hf : Periodic f c) (hc : c ≠ 0) (hf_cont : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  have h := (hf.comp fun y ↦ ‖y‖).bddAbove_range_of_continuous hc hf_cont.norm
  rcases h.exists_ge 0 with ⟨C, _, hC⟩
  exact ⟨C, fun x ↦ by simpa using hC ‖f x‖⟩

end PeriodicUtil

section HasTemperateGrowth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- TODO: Could generalize beyond `ℝ`? Not necessary at this stage.
theorem Periodic.hasTemperateGrowth {f : ℝ → F} {c : ℝ}
    (hf : Periodic f c) (hc : c ≠ 0) (hf_smooth : ContDiff ℝ ∞ f) : f.HasTemperateGrowth := by
  refine ⟨hf_smooth, fun n ↦ ⟨0, ?_⟩⟩
  simpa using (hf.iteratedFDeriv ℝ n).exists_bound_of_continuous hc
    (hf_smooth.continuous_iteratedFDeriv (by norm_cast; simp))

end HasTemperateGrowth

end Function

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace Real

theorem cos_hasTemperateGrowth : cos.HasTemperateGrowth :=
  cos_periodic.hasTemperateGrowth two_pi_pos.ne' contDiff_cos

theorem sin_hasTemperateGrowth : sin.HasTemperateGrowth :=
  sin_periodic.hasTemperateGrowth two_pi_pos.ne' contDiff_sin

-- theorem bilinear_right_hasTemperateGrowth (L : V →L[ℝ] W →L[ℝ] ℝ) (v : V) :
--     (L v ·).HasTemperateGrowth := (L v).hasTemperateGrowth

-- theorem bilinear_left_hasTemperateGrowth (L : V →L[ℝ] W →L[ℝ] ℝ) (w : W) :
--     (L · w).HasTemperateGrowth := (L.flip w).hasTemperateGrowth

-- theorem real_inner_right_hasTemperateGrowth (a : U) : (inner a : U → ℝ).HasTemperateGrowth :=
--     bilinear_right_hasTemperateGrowth (innerSL ℝ) a

-- theorem real_inner_left_hasTemperateGrowth (a : U) : (inner · a : U → ℝ).HasTemperateGrowth :=
--     bilinear_left_hasTemperateGrowth (innerSL ℝ) a

end Real

namespace Complex

open scoped Real

theorem exp_ofReal_mul_I_periodic : Function.Periodic (fun x : ℝ ↦ exp (x * I)) (2 * π) :=
  fun x ↦ by simp [add_mul, exp_add]

theorem exp_ofReal_mul_I_hasTemperateGrowth : Function.HasTemperateGrowth fun x : ℝ ↦ exp (x * I) :=
  exp_ofReal_mul_I_periodic.hasTemperateGrowth Real.two_pi_pos.ne'
    (ofRealCLM.contDiff.mul contDiff_const).cexp

theorem exp_const_ofReal_I_periodic (a : ℝ) :
    Function.Periodic (fun x : ℝ ↦ exp (a * x * I)) (a⁻¹ * (2 * π)) := by
  simpa using exp_ofReal_mul_I_periodic.const_mul a

-- TODO: Generalize to `fun x : V ↦ exp (inner a x * I)`
theorem exp_const_ofReal_I_hasTemperateGrowth (a : ℝ) :
    (fun x : ℝ ↦ exp (a * x * I)).HasTemperateGrowth := by
  norm_cast
  exact .comp exp_ofReal_mul_I_hasTemperateGrowth (ContinuousLinearMap.mul ℝ ℝ a).hasTemperateGrowth

-- theorem exp_const_inner_mul_I_hasTemperateGrowth (a : V) :
--     Function.HasTemperateGrowth fun x : V ↦ exp ((inner a x : ℝ) * I) :=
--   exp_ofReal_mul_I_hasTemperateGrowth.comp (Real.const_inner_hasTemperateGrowth a)

-- theorem exp_inner_const_mul_I_hasTemperateGrowth (a : V) :
--     Function.HasTemperateGrowth fun x : V ↦ exp ((inner x a : ℝ) * I) :=
--   exp_ofReal_mul_I_hasTemperateGrowth.comp (Real.inner_const_hasTemperateGrowth a)

end Complex

namespace Real

-- TODO: Move?
theorem fourierChar_periodic : (𝐞 ·).Periodic 1 := fun x ↦ by
  simp [fourierChar, mul_add]

theorem coe_fourierChar_periodic : (𝐞 · : ℝ → ℂ).Periodic 1 := by
  simp [fourierChar, mul_add]

theorem fourierChar_hasTemperateGrowth : (𝐞 · : ℝ → ℂ).HasTemperateGrowth :=
  coe_fourierChar_periodic.hasTemperateGrowth one_ne_zero contDiff_fourierChar

-- Mimic structure of `hasFDerivAt_fourierChar_neg_bilinear_right`

theorem fourierChar_inner_right_hasTemperateGrowth (a : U) :
    (fun x ↦ (𝐞 (inner a x) : ℂ)).HasTemperateGrowth :=
  .comp fourierChar_hasTemperateGrowth (innerSL ℝ a).hasTemperateGrowth

theorem fourierChar_inner_left_hasTemperateGrowth (a : U) :
    (fun x ↦ (𝐞 (inner x a) : ℂ)).HasTemperateGrowth :=
  .comp fourierChar_hasTemperateGrowth ((innerSL ℝ).flip a).hasTemperateGrowth

theorem fourierChar_neg_inner_right_hasTemperateGrowth (a : U) :
    (fun x ↦ (𝐞 (-inner a x) : ℂ)).HasTemperateGrowth :=
  .comp fourierChar_hasTemperateGrowth (-innerSL ℝ a).hasTemperateGrowth

theorem fourierChar_neg_inner_left_hasTemperateGrowth (a : U) :
    (fun x ↦ (𝐞 (-inner x a) : ℂ)).HasTemperateGrowth :=
  .comp fourierChar_hasTemperateGrowth (-(innerSL ℝ).flip a).hasTemperateGrowth

end Real
