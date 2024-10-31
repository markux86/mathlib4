/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Topology.Compactification.OnePointEquiv
import Mathlib.Topology.Compactification.OnePointRealLemmas
-- abs_le_inv, open_nonzero, symmetrize, dist_cone_pos, dist_cone_neg, pos_or_neg
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Topology.Instances.Real
-- import Mathlib.Algebra.Order.Group.Unbundled.Abs
-- import Mathlib.Topology.UniformSpace.Basic
-- import Mathlib.Algebra.EuclideanDomain.Field
-- import Mathlib.Algebra.EuclideanDomain.Basic
-- import Mathlib.Analysis.RCLike.Basic
-- import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Homeomorphism between one-point compactification and projective space


We prove that slope, suitably defined, is a homeomorphism from ℙ ℝ (Fin 2 → ℝ) to OnePoint ℝ.
In particular with our notion of slope, 1 ÷ 0 = ∞.

## Main results

* `onepointhomeo`: The desired homeomorphism.

## Tags

homeomorphism, projective
-/

open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization


open Classical

/-- -/
noncomputable def OnePoint_div {K : Type} [DivisionRing K] (a : K) (r : K): OnePoint K :=
    ite (r ≠ 0) (a / r) ∞

/-- -/
infix:50 " ÷ " => OnePoint_div


/-- -/
lemma div_slope_well_defined {K : Type} [Field K]
    (a b : { v : Fin 2 → K // v ≠ 0 })
    (h : ∃ c : Kˣ, (fun m : Kˣ ↦ m • b.1) c = a.1) :
    (fun u ↦ u.1 0 ÷ u.1 1) a = (fun u ↦ u.1 0 ÷ u.1 1) b := by
  obtain ⟨c,hc⟩ := h
  simp_all only
  rw [← hc]; unfold OnePoint_div; simp only [ne_eq, Fin.isValue, Pi.smul_apply, ite_not]
  split_ifs with hbc hb hb
  · rfl
  · simp_all only [ne_eq, OnePoint.infty_ne_coe]
    apply hb;exact (Units.mul_right_eq_zero c).mp hbc
  · rw [hb] at hbc;simp at hbc
  · apply congrArg some
    field_simp
    show c * b.1 0 * b.1 1 = b.1 0 * (c * b.1 1)
    ring

/-- Function underlying homeomorphism. -/
noncomputable def div_slope (p : ℙ ℝ (Fin 2 → ℝ)) : OnePoint ℝ :=
  Quotient.lift
    (fun u : { v : Fin 2 → ℝ // v ≠ 0} ↦
      OnePoint_div (u.1 0) (u.1 1)) div_slope_well_defined p

/-- A pair is nonzero if the corresponding tuple is nonzero. -/
lemma nonzero_of_nonzero (a : {v : Fin 2 → ℝ // v ≠ 0}) :
    (a.1 0, a.1 1) ≠ 0 := by
  have := a.2
  contrapose this
  simp_all only [ne_eq, Prod.mk_eq_zero, not_and, Classical.not_imp, Decidable.not_not]
  ext z
  fin_cases z <;> simp_all


/-- Equivalence between two parametrizations of "lines through the origin". -/
noncomputable def tupFinNonzero :
  { p : ℝ × ℝ // p ≠ 0} ≃ {p : Fin 2 → ℝ // p ≠ 0} where
  toFun := by
    intro p
    exact ⟨![p.1.1, p.1.2], by
      have := p.2
      contrapose this
      simp_all only [ne_eq, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and,
        Classical.not_imp, Decidable.not_not]
      ext <;> simp_all
    ⟩
  invFun := by
    intro p
    exact ⟨(p.1 0,p.1 1),by
      have := p.2
      contrapose this
      simp_all only [ne_eq, Prod.mk_eq_zero, not_and, Classical.not_imp, Decidable.not_not]
      ext i
      simp_all only [Pi.zero_apply]
      fin_cases i <;> tauto
    ⟩
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp only [ne_eq, Fin.isValue]
    ext i
    simp_all only
    fin_cases i <;> tauto

/-- Equivalence between two forms of projective line. -/
noncomputable def projFinTup :
  ℙ ℝ (Fin 2 → ℝ) ≃ ℙ ℝ (ℝ × ℝ) where
  toFun := Quotient.lift
      (fun w : {p : Fin 2 → ℝ // p ≠ 0} => (Quotient.mk _ (tupFinNonzero.invFun w) : ℙ ℝ (ℝ × ℝ)))
      (fun u v huv => Quotient.sound <| by
        obtain ⟨c,hc⟩ := huv
        use c
        aesop)
  invFun := by
    let f : { p : ℝ × ℝ // p ≠ 0} → ℙ ℝ (Fin 2 → ℝ) :=
      fun w => Quotient.mk _ (tupFinNonzero.toFun w)
    refine Quotient.lift f (by
      intro a b hab; unfold f;
      refine Quotient.sound ?_
      obtain ⟨c,hc⟩ := hab
      use c
      unfold tupFinNonzero
      ext i
      fin_cases i <;>
      · simp only [ne_eq, Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero]
        rw [← hc]
        simp
    )
  left_inv := by
    apply Quotient.ind
    intro a
    simp
  right_inv := by
    apply Quotient.ind
    intro a
    simp

/-- Express div_slope in terms of OnePointEquiv. -/
theorem reconcile :
    div_slope = (OnePoint.equivProjectivization ℝ).invFun ∘ projFinTup.toFun := by
  ext p
  exact @Quotient.ind {v : Fin 2 → ℝ // v ≠ 0}
    (projectivizationSetoid ℝ (Fin 2 → ℝ))
    (fun p => div_slope p = (OnePoint.equivProjectivization ℝ).symm (projFinTup p))
    (by
      intro v
      unfold div_slope projFinTup OnePoint.equivProjectivization tupFinNonzero
      unfold OnePoint_div
      simp only [ne_eq, Fin.isValue, ite_not, Quotient.lift_mk, Equiv.invFun_as_coe,
        Equiv.coe_fn_symm_mk, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      split_ifs with g₀
      · simp_rw [g₀]
        rw [Projectivization.lift]
        aesop
      · rw [Projectivization.lift]
        simp_all only [ne_eq, Quotient.lift_mk, ite_false]
        ring_nf
    ) p

/-- Equivalence OnePoint ℝ ≃ ℙ ℝ (Fin 2 → ℝ). -/
noncomputable def div_slope_equiv :
  OnePoint ℝ ≃ ℙ ℝ (Fin 2 → ℝ) where
  toFun     := projFinTup.invFun ∘ (OnePoint.equivProjectivization ℝ).toFun
  invFun    := div_slope
  left_inv  := by
    rw [reconcile]
    show Function.LeftInverse (⇑(OnePoint.equivProjectivization ℝ).symm ∘ ⇑projFinTup)
      (⇑projFinTup.symm ∘ ⇑(OnePoint.equivProjectivization ℝ))
    intro
    simp
  right_inv := by
    rw [reconcile]
    show Function.RightInverse ((OnePoint.equivProjectivization ℝ).invFun ∘ projFinTup.toFun)
      (projFinTup.invFun ∘ (OnePoint.equivProjectivization ℝ).toFun)
    intro
    simp

/-- Division is continnuous. -/
lemma continuous_slope_nonzero_case {x : { v : Fin 2 → ℝ // v ≠ 0 }} (hx : ¬x.1 1 = 0) :
    ContinuousAt (fun u ↦ u.1 0 ÷ u.1 1) x := by
  have : (fun u ↦ u.1 0 ÷ u.1 1) =ᶠ[nhds x] fun v ↦ OnePoint.some (v.1 0 / v.1 1) := by
      unfold Filter.EventuallyEq OnePoint_div
      simp only [ne_eq, Fin.isValue, ite_not, ite_eq_right_iff,
        OnePoint.infty_ne_coe, imp_false];
      exact eventually_nhds_iff.mpr (open_nonzero hx)
  rw [continuousAt_congr this]

  apply ContinuousAt.comp'
  · exact Continuous.continuousAt OnePoint.continuous_coe
  refine ContinuousAt.div₀ ?_ ?_ hx

  · exact ContinuousAt.comp (continuousAt_apply 0 x.1) continuousAt_subtype_val
  · exact ContinuousAt.comp (continuousAt_apply 1 x.1) continuousAt_subtype_val

/-- Auxiliary nhds lemma.  -/
lemma slope_open_nonzero
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₁ : IsOpen (OnePoint.some ⁻¹' t))
    {a : { v : Fin 2 → ℝ // ¬v = 0 }}
    (ha : (if a.1 1 = 0 then ∞ else some (a.1 0 / a.1 1)) ∈ t)
    (H : ¬a.1 1 = 0) :
    (fun u : { v : Fin 2 → ℝ // v ≠ 0} ↦
    if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t ∈ nhds a := by
  rw [if_neg H] at ha
  have Q := continuous_slope_nonzero_case H
  rw [continuousAt_def] at Q
  unfold OnePoint_div at Q
  simp only [ne_eq, Fin.isValue, ite_not] at Q
  apply Q
  rw [if_neg H]
  refine IsOpen.mem_nhds ?_ ha
  refine OnePoint.isOpen_def.mpr ?_
  tauto

/-- Auxiliary uniformity lemma.  -/
lemma slope_uniform_of_compact_pos {n : ℕ} {i j : Fin n}
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin n → ℝ // v ≠ 0 }}
    (H : a.1 j = 0)
    (hl : a.1 i > 0) : ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 j = 0 then ∞ else some (u.1 i / u.1 j)) ⁻¹' t :=  by
  have W := IsCompact.isBounded (ht₀)
  rw [Bornology.isBounded_def] at W
  simp only [Real.cobounded_eq, compl_compl, Filter.mem_sup, Filter.mem_atBot_sets,
    Set.mem_preimage, Filter.mem_atTop_sets, ge_iff_le] at W
  obtain ⟨⟨a₀,ha₀⟩,⟨a₁,ha₁⟩⟩ := W

  let amax := max |a₀| |a₁|
  have hamax : ∀ b : ℝ, b ≤ -amax ∨ amax ≤ b → some b ∈ t := by
    apply symmetrize;exact ha₀;exact ha₁
  let Q := dist_cone_pos H hl (show amax ≥ 0 by positivity)
  obtain ⟨δ,hδ⟩ := Q
  use {(u,v) | dist u.1 v.1 < δ}
  constructor
  · refine Metric.dist_mem_uniformity ?h.left.ε0
    tauto
  · intro x h_x
    simp only [ne_eq] at h_x
    have hx : dist a x < δ := h_x
    clear h_x
    simp only [ne_eq, Fin.isValue, Set.mem_preimage]
    by_cases hz : x.1 j = 0
    · rw [hz];simp only [↓reduceIte];tauto
    · rw [if_neg hz]
      apply hamax
      by_cases hpos : x.1 j > 0
      · right
        have : dist a x = dist a.1 x.1 := rfl
        have hδ' := hδ.2 x.1 (by rw [dist_comm];linarith)
        tauto
      · left
        have h₁: x.1 j < 0 := lt_of_le_of_ne (le_of_not_lt hpos) hz
        rw [dist_comm] at hx
        have : dist x.1 a.1 < δ := hx
        have h₀: dist x.1 a.1 ≤ δ := by linarith
        exact (hδ.2 x h₀).1 h₁

/-- Auxiliary uniformity lemma.  -/
lemma slope_uniform_of_compact_neg {n : ℕ} {i j : Fin n} {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ) (ht₂ : ∞ ∈ t)
    {a : { v : Fin n → ℝ // v ≠ 0 }} (H : a.1 j = 0) (hl : a.1 i < 0) :
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 j = 0 then ∞ else some (u.1 i / u.1 j)) ⁻¹' t :=  by
  have W := IsCompact.isBounded (ht₀)
  rw [Bornology.isBounded_def] at W
  simp only [Real.cobounded_eq, compl_compl, Filter.mem_sup, Filter.mem_atBot_sets,
    Set.mem_preimage, Filter.mem_atTop_sets, ge_iff_le] at W
  obtain ⟨⟨a₀,ha₀⟩,⟨a₁,ha₁⟩⟩ := W

  let amax := max |a₀| |a₁|
  have hamax : ∀ b : ℝ, b ≤ -amax ∨ amax ≤ b → some b ∈ t := by
    apply symmetrize;exact ha₀;exact ha₁
  let Q := dist_cone_neg H hl (show amax ≥ 0 by positivity)
  obtain ⟨δ,hδ⟩ := Q
  use {(u,v) | dist u v < δ}
  constructor
  · exact Metric.dist_mem_uniformity hδ.1
  · intro x h_x
    have hx : dist a x < δ := h_x
    clear h_x
    simp only [ne_eq, Fin.isValue, Set.mem_preimage]
    by_cases X : x.1 j = 0
    · rw [X];simp only [↓reduceIte];tauto
    · rw [if_neg X];
      apply hamax
      by_cases hpos : x.1 j > 0
      · left
        have : dist a x = dist a.1 x.1 := rfl
        have hδ' := hδ.2 x.1 (by rw [dist_comm];linarith)
        tauto
      · right
        have hneg: x.1 j < 0 := lt_of_le_of_ne (le_of_not_lt hpos) X
        rw [dist_comm] at hx
        have : dist x.1 a.1 < δ := hx
        have h₀: dist x.1 a.1 ≤ δ := by linarith
        exact (hδ.2 x h₀).2 hneg

/-- -/
lemma slopeUniform_of_compact {n : ℕ} {j : Fin n}
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin n → ℝ // v ≠ 0 }}
    (H : a.1 j = 0) :
    ∃ i,
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 j = 0 then ∞ else some (u.1 i / u.1 j)) ⁻¹' t := by
  obtain ⟨i,hi⟩ := @posOrNeg n a
  use i
  cases hi with
  |inl hl => exact slope_uniform_of_compact_pos ht₀ ht₂ H hl
  |inr hr => exact slope_uniform_of_compact_neg ht₀ ht₂ H hr

/-- Auxiliary uniformity lemma requiring Fin 2.  -/
lemma slope_uniform_of_compact
    {t : Set (OnePoint ℝ)}
    (ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ)
    (ht₂ : ∞ ∈ t)
    {a : { v : Fin 2 → ℝ // v ≠ 0 }}
    (H : a.1 1 = 0) :
    ∃ V ∈ uniformity { v // ¬v = 0 },
    UniformSpace.ball a V ⊆ (fun u ↦ if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t := by
  cases (pos_or_neg H) with
  |inl hl => exact slope_uniform_of_compact_pos ht₀ ht₂ H hl
  |inr hr => exact slope_uniform_of_compact_neg ht₀ ht₂ H hr

/-- Auxiliary openness lemma.  -/
lemma slope_open
    {t : Set (OnePoint ℝ)}
    (h_t : IsOpen t ∧ ∞ ∈ t) :
    IsOpen ((fun u : { v : Fin 2 → ℝ // v ≠ 0 }
    ↦ if u.1 1 = 0 then ∞ else some (u.1 0 / u.1 1)) ⁻¹' t) := by
  rw [OnePoint.isOpen_def] at h_t
  have ht₀ : IsCompact (OnePoint.some ⁻¹' t)ᶜ := by tauto
  have ht₁ : IsOpen (OnePoint.some ⁻¹' t) := by tauto
  have ht₂ : ∞ ∈ t := by tauto
  clear h_t
  rw [isOpen_iff_nhds]
  intro a ha
  simp_all only [ne_eq, Set.mem_preimage, Filter.le_principal_iff]
  by_cases H : a.1 1 = 0
  · have Q := slope_uniform_of_compact ht₀ ht₂ H
    obtain ⟨V,hV⟩ := Q
    rw [nhds_eq_comap_uniformity]
    simp only [Fin.isValue, Filter.mem_comap]
    use V
    simp_all only [div_zero, ite_true, ne_eq,
      true_and];tauto
  · exact slope_open_nonzero ht₀ ht₁ ha H

/-- Auxiliary continuity lemma.  -/
lemma continuous_slope_zero_case (x : { v : Fin 2 → ℝ // v ≠ 0 }) (H₁ : x.1 1 = 0) :
    ContinuousAt (fun u ↦ u.1 0 ÷ u.1 1) x := by
  unfold OnePoint_div
  rw [continuousAt_def]
  intro A hA
  rw [mem_nhds_iff] at *
  obtain ⟨t,ht⟩ := hA
  use (fun u ↦ if u.1 1 = 0 then ∞ else Option.some (u.1 0 / u.1 1)) ⁻¹' t
  constructor
  · intro a ha
    simp only [ne_eq, Fin.isValue, Set.mem_preimage] at ha
    simp only [ne_eq, Fin.isValue, ite_not, Set.mem_preimage]
    split_ifs with h₀
    · simp_all only [ne_eq, not_true_eq_false, div_zero, ite_false, ite_true]
      tauto
    · rw [if_neg h₀] at *; tauto
  · simp_all only [ne_eq, not_true_eq_false, div_zero, ite_false, Set.mem_preimage, ite_true,
    and_true]
    apply slope_open
    tauto

/-- Auxiliary continuity lemma.  -/
theorem div_slope_continuous_unlifted :
    Continuous fun u : { v : Fin 2 → ℝ // v ≠ 0 } ↦ (u.1 0) ÷ (u.1 1) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases H₁ : x.1 1 = 0
  · apply continuous_slope_zero_case;tauto
  · apply continuous_slope_nonzero_case;tauto

/-- Topology on projectivization. -/
instance {n : ℕ}: TopologicalSpace (ℙ ℝ (Fin n → ℝ)) := instTopologicalSpaceQuot

/-- div_slope is continuous. -/
theorem div_slope_continuous : Continuous div_slope := by
  apply continuous_quot_lift
  apply div_slope_continuous_unlifted

/-- List from unit circle to projectivization. -/
def lift_unit_circle {n:ℕ}  : {v : Fin n → ℝ // dist v 0 = 1} → ℙ ℝ (Fin n → ℝ) := by
  intro v
  exact mk' ℝ ⟨v.1,by
    intro hc;
    have : dist v.1 0 = 1 := v.2
    rw [hc] at this;simp_all
  ⟩

/-- List from unit circle to projectivization is surjective. -/
lemma surjective_lift_unit_circle {n:ℕ} :
    Function.Surjective (@lift_unit_circle n) :=
  Quotient.ind (fun x ↦ by
    have := x.2
    have : ‖x.1‖ ≠ 0 := by simp_all
    use ⟨‖x.1‖⁻¹ • x.1, by simp only [ne_eq, dist_zero_right]; rw [norm_smul]; field_simp⟩
    unfold lift_unit_circle; simp only [ne_eq, mk'_eq_mk]
    show mk ℝ (‖x.1‖⁻¹ • x.1) _ = mk ℝ x.1 _
    rw [mk_eq_mk_iff]
    use Units.mk ‖x.1‖⁻¹ ‖x.1‖ (by field_simp) (by field_simp)
    simp
  )

/-- List from unit circle to projectivization is continuous. -/
lemma continuous_lift_unit_circle {n:ℕ} : Continuous (@lift_unit_circle n) := by
  unfold lift_unit_circle
  refine Continuous.comp' ?hg ?hf;
  · exact { isOpen_preimage := fun s a ↦ a }
  exact Isometry.continuous fun x1 ↦ congrFun rfl

/-- Unit circle is compact. -/
instance {n:ℕ} : CompactSpace {v : Fin n → ℝ // dist v 0 = 1} := Metric.sphere.compactSpace 0 1

/-- Projectivization is compact. -/
instance {n:ℕ} : CompactSpace (ℙ ℝ (Fin n → ℝ)) := by
  let Q := IsCompact.image CompactSpace.isCompact_univ (@continuous_lift_unit_circle n)
  have : lift_unit_circle '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective (@surjective_lift_unit_circle n)
  exact {
      isCompact_univ := by rw [← this];exact Q
  }

/-- The real projective line ℙ ℝ (Fin 2 → ℝ) and OnePoint ℝ are homeomorphic.-/
noncomputable def OnePointHomeo : Homeomorph (ℙ ℝ (Fin 2 → ℝ)) (OnePoint ℝ) :=
  Continuous.homeoOfEquivCompactToT2 (f := div_slope_equiv.symm) div_slope_continuous

/-- The real projective line is a Hausdorff space. -/
instance :  T2Space (ℙ ℝ (Fin 2 → ℝ)) := Homeomorph.t2Space OnePointHomeo.symm


/-- Uniqueness-based proof that
  the real projective line ℙ ℝ (Fin 2 → ℝ) and OnePoint ℝ are homeomorphic. -/
noncomputable def OnePointHomeo' : Homeomorph (ℙ ℝ (Fin 2 → ℝ)) (OnePoint ℝ) := by
    have := @OnePoint.equivOfIsEmbeddingOfRangeEq ℝ (ℙ ℝ (Fin 2 → ℝ)) _ _ _ _
        ⟦ ⟨![1,0],by simp⟩ ⟧ (fun r => ⟦ ⟨![r,1],by simp⟩ ⟧) (by
        constructor
        · refine isInducing_iff_nhds.mpr ?toIsInducing.a
          intro x
          ext s
          simp
          rw [mem_nhds_iff_exists_Ioo_subset ]
          simp_rw [mem_nhds_iff]
          constructor
          · intro h
            obtain ⟨l,hl⟩ := h
            obtain ⟨u,hu⟩ := hl
            let f := fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ))
            have If : IsOpenMap f := by
                have : f = fun r : ℝ => div_slope_equiv r := by
                    aesop
                rw [this]
                apply IsOpenMap.comp
                ·   intro S hS
                    have hc := OnePointHomeo.continuous_toFun
                    have hi : IsOpen ((OnePointHomeo.toFun) ⁻¹' S) := by
                        exact hc.isOpen_preimage S hS
                    show IsOpen (⇑div_slope_equiv '' S)
                    have : ⇑div_slope_equiv '' S = OnePointHomeo.toFun ⁻¹' S := by
                        aesop
                    rw [this]
                    exact hi
                · exact OnePoint.isOpenMap_coe
            use f '' (Set.Ioo l u)
            constructor
            · use f '' (Set.Ioo l u)
              constructor
              · aesop
              · constructor
                · show IsOpen ((fun r ↦ ⟦⟨![r, 1], by simp⟩⟧) '' Set.Ioo l u)

                  apply If
                  exact isOpen_Ioo
                · simp
                  use x
                  aesop
            simp_all
            intro a ha
            simp at ha
            apply hu.2
            obtain ⟨y,hy⟩ := ha
            have := hy.2
            simp at this
            have : y = a := by
                simp_all only [ne_eq, f]
                obtain ⟨left, right⟩ := hu
                obtain ⟨left_1, right_1⟩ := hy
                obtain ⟨left, right_2⟩ := left
                obtain ⟨left_1, right_3⟩ := left_1
                have : ![y, 1] = ![a, 1] := by
                    clear left right_2 left_1 right_3 right f l u s x
                    rw [Quotient.eq] at right_1
                    obtain ⟨c,hc⟩ := right_1
                    simp at hc
                    have : c • a = c * a := rfl
                    rw [this] at hc
                    have : c • 1 = c.1 * 1 := rfl
                    rw [this] at hc
                    have g₀ := congrFun hc 0
                    have g₁ := congrFun hc 1
                    simp_all
                have := congrFun this 0
                aesop
            aesop
          · intro h
            obtain ⟨t,ht⟩ := h
            obtain ⟨t₁,ht₁⟩ := ht.1
            have : Continuous (fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ))) := by
                apply Continuous.comp'
                exact { isOpen_preimage := fun s a ↦ a }
                apply Continuous.subtype_mk
                refine continuous_pi ?hf.h.h
                intro i
                fin_cases i
                simp
                exact continuous_id'
                simp
                exact continuous_const
            let u := (fun r ↦ (⟦⟨![r, 1], by simp⟩⟧ : ℙ ℝ (Fin 2 → ℝ))) ⁻¹' t₁
            have h₀ : x ∈ u := by aesop
            have h₁ : IsOpen u := by
                refine this.isOpen_preimage t₁ ?_
                tauto
            rw [← mem_nhds_iff_exists_Ioo_subset]
            have h₂ : u ∈ nhds x := by exact IsOpen.mem_nhds h₁ h₀
            have h₃ : u ⊆ s := by
                intro z hz
                change (z ∈ (fun r ↦ ⟦⟨![r, 1], by simp⟩⟧) ⁻¹' t₁) at hz
                simp at hz
                apply ht.2
                simp_all
                apply ht₁.1 hz
            exact Filter.mem_of_superset h₂ h₃
        · intro x y h
          simp at h
          rw [Quotient.eq] at h
          obtain ⟨c,hc⟩ := h
          simp at hc
          have g₀: c • y = c.1 * y := rfl
          rw [g₀] at hc
          have g₁: c • 1 = c.1 * 1 := rfl
          rw [g₁] at hc
          clear g₀ g₁
          have h₁ := congrFun hc 1
          have h₀ := congrFun hc 0
          simp_all
        )
        (by
            apply Set.ext
            apply Quotient.ind
            intro p
            simp
            constructor
            · intro ⟨y,hy⟩
              simp
              intro hc
              have h := Eq.trans hy hc
              clear hy hc p
              simp at h
              rw [Quotient.eq] at h
              obtain ⟨c,hc⟩ := h
              simp at hc
              have : ![c • 1, 0] 1 = ![y, 1] 1 := congrFun hc 1
              simp_all
            · intro h
              rw [Quotient.eq] at h
              have : ¬ ∃ c : ℝˣ, (fun m ↦ m • ![1, 0]) c = p.1 := by
                contrapose h
                simp_all only [Decidable.not_not]
                exact h
              by_cases H : p.1 1 = 0
              · exfalso
                apply this
                use ⟨p.1 0, 1 / p.1 0, by
                    simp
                    have := p.2;contrapose this;simp_all
                    ext i
                    fin_cases i
                    · contrapose this
                      simp_all
                    · exact H, by
                    have : p.1 0 ≠ 0 := by
                        have := p.2
                        contrapose this
                        simp_all
                        ext i
                        fin_cases i
                        · exact this
                        · exact H
                    simp
                    exact inv_mul_cancel₀ this
                ⟩
                simp
                ext i
                fin_cases i
                · simp
                · simp;tauto
              · use p.1 0 / p.1 1
                symm
                apply Quotient.sound
                use ⟨p.1 1, 1 / p.1 1,by
                    simp
                    have := p.2;contrapose this;simp_all
                    , by
                    have : p.1 1 ≠ 0 := by
                        have := p.2
                        contrapose this
                        simp_all
                    simp
                    exact inv_mul_cancel₀ this                ⟩
                simp
                ext i
                fin_cases i
                · simp;ring_nf;rw [mul_comm,← mul_assoc];
                  aesop
                · simp
        )
    exact this.symm
