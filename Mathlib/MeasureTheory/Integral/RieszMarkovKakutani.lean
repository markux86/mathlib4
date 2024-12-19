/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable


/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X`. As a special case, the statements about linear functionals on bounded continuous
functions follows.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of a locally compact space X, rather than the usual construction of open sets in the
literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

section Λ_mono

lemma Λ_mono (f₁ f₂ : C_c(X, ℝ≥0)) (h : f₁.1 ≤ f₂.1) : Λ f₁ ≤ Λ f₂ := by
  obtain ⟨g, hg⟩ := exist_add_eq f₁ f₂ h
  simp only [← hg, map_add, le_add_iff_nonneg_right, zero_le]

end Λ_mono

/-- Given a positive linear functional `Λ` on continuous compactly supported functions on `X`
with values in `ℝ≥0`, for `K ⊆ X` compact define `λ(K) = inf {Λf | 1≤f on K}`.
When `X` is a locally compact T2 space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
  sInf (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })

section RieszMonotone

variable [T2Space X] [LocallyCompactSpace X]

/-- For any compact subset `K ⊆ X`, there exist some compactly supported continuous nonnegative
functions `f` on `X` such that `f ≥ 1` on `K`. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    exact closure_mono interior_subset
  obtain ⟨f, hsuppfsubV, hfeq1onK, hfinicc⟩ :=
    exists_tsupport_one_of_isOpen_isClosed isOpen_interior hIsCompact_closure_interior
      (IsCompact.isClosed K.2) hKsubintV
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hVcp (isClosed_tsupport f)
      (Set.Subset.trans hsuppfsubV interior_subset)
  use nnrealPart ⟨f, hfHasCompactSupport⟩
  intro x hx
  apply le_of_eq
  simp only [nnrealPart_apply, CompactlySupportedContinuousMap.coe_mk]
  rw [← Real.toNNReal_one, Real.toNNReal_eq_toNNReal_iff (zero_le_one' ℝ) (hfinicc x).1]
  exact hfeq1onK.symm hx

/-- Riesz content `λ` (associated with a positive linear functional `Λ`) is
monotone: if `K₁ ⊆ K₂` are compact subsets in `X`, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ :=
  csInf_le_csInf (OrderBot.bddBelow _) (rieszContentAux_image_nonempty Λ K₂)
    (image_subset Λ (setOf_subset_setOf.mpr fun _ f_hyp x x_in_K₁ => f_hyp x (h x_in_K₁)))

end RieszMonotone

section RieszSubadditive

/-- Any compactly supported continuous nonnegative `f` such that `f ≥ 1` on `K` gives an upper bound
on the content of `K`; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ≥0)} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
    rieszContentAux Λ K ≤ Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

variable [T2Space X] [LocallyCompactSpace X]

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a compactly supported continuous
nonnegative function `f` on `X` such that `f ≥ 1` on `K` and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ f : C_c(X, ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

/-- The Riesz content `λ` associated to a given positive linear functional `Λ` is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
    rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive


section PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

lemma exists_continuous_add_one_of_isCompact_nnreal
    {s₀ s₁ : Set X} {t : Set X} (s₀_compact : IsCompact s₀) (s₁_compact : IsCompact s₁)
    (t_compact : IsCompact t) (disj : Disjoint s₀ s₁) (hst : s₀ ∪ s₁ ⊆ t) :
    ∃ (f₀ f₁ : C_c(X, ℝ≥0)), EqOn f₀ 1 s₀ ∧ EqOn f₁ 1 s₁ ∧ EqOn (f₀ + f₁) 1 t := by
  set so : Fin 2 → Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) :  IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₁_compact
  have hsot : t ⊆ ⋃ j, so j := by
    rw [hso]
    simp only [Fin.isValue]
    intro x hx
    rw [mem_iUnion]
    rw [← subset_compl_iff_disjoint_right, ← compl_compl s₀, compl_subset_iff_union] at disj
    have h : x ∈ s₀ᶜ ∨ x ∈ s₁ᶜ := by
      rw [← mem_union, disj]
      trivial
    apply Or.elim h
    · intro h0
      use 0
      simp only [Fin.isValue, ↓reduceIte]
      exact h0
    · intro h1
      use 1
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      exact h1
  obtain ⟨f, f_supp_in_so, sum_f_one_on_t, f_in_icc, f_hcs⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact soopen t_compact hsot
  use (nnrealPart (⟨f 1, f_hcs 1⟩ : C_c(X, ℝ))),
    (nnrealPart (⟨f 0, f_hcs 0⟩ : C_c(X, ℝ)))
  simp only [Fin.isValue, CompactlySupportedContinuousMap.coe_add]
  have sum_one_x (x : X) (hx : x ∈ t) : (f 0) x + (f 1) x = 1 := by
    simpa only [Finset.sum_apply, Fin.sum_univ_two, Fin.isValue, Pi.one_apply]
      using sum_f_one_on_t hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 0) x = 0 := by
      rw [← nmem_support]
      have : s₀ ⊆ (tsupport (f 0))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 0))
        rw [hso]
        simp only [Fin.isValue, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.1 hx), this]
    exact Eq.symm (AddZeroClass.zero_add ((f 1) x))
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 1) x = 0 := by
      rw [← nmem_support]
      have : s₁ ⊆ (tsupport (f 1))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 1))
        rw [hso]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.2 hx), this]
    exact Eq.symm (AddMonoid.add_zero ((f 0) x))
  · intro x hx
    simp only [Fin.isValue, Pi.add_apply, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply]
    rw [Real.toNNReal_add_toNNReal (f_in_icc 1 x).1 (f_in_icc 0 x).1, add_comm]
    simp only [Fin.isValue, Real.toNNReal_eq_one]
    exact sum_one_x x hx

end PartitionOfUnity

section RieszContentAdditive

variable [T2Space X] [LocallyCompactSpace X]

lemma rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X}
    (disj : Disjoint (K₁ : Set X) K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : ∀ x ∈ K₁ ⊔ K₂, x ∈ support f := by
    intro x hx
    rw [mem_support]
    exact Ne.symm (ne_of_lt <| lt_of_lt_of_le (zero_lt_one' ℝ≥0) (hf x hx))
  have hsubsuppf : (K₁ : Set X) ∪ (K₂ : Set X) ⊆ tsupport f := subset_trans hsuppf subset_closure
  obtain ⟨g₁, g₂, hg₁, hg₂, sum_g⟩ := exists_continuous_add_one_of_isCompact_nnreal K₁.isCompact'
    K₂.isCompact' f.hasCompactSupport'.isCompact disj hsubsuppf
  have f_eq_sum : f = g₁ * f + g₂ * f := by
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mul,
      Pi.add_apply, Pi.mul_apply, NNReal.coe_add, NNReal.coe_mul,
      Eq.symm (RightDistribClass.right_distrib _ _ _), ← NNReal.coe_add, ← Pi.add_apply]
    by_cases h : f x = 0
    · rw [h]
      simp only [NNReal.coe_zero, NNReal.coe_add, mul_zero]
    · push_neg at h
      simp only [CompactlySupportedContinuousMap.coe_add, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap] at sum_g
      rw [sum_g (mem_of_subset_of_mem subset_closure (mem_support.mpr h))]
      simp only [Pi.one_apply, NNReal.coe_one, one_mul]
  rw [← Λf_eq_b, f_eq_sum, map_add]
  have aux₁ : ∀ x ∈ K₁, 1 ≤ (g₁ * f) x := by
    intro x x_in_K₁
    simp [hg₁ x_in_K₁, hf x (mem_union_left _ x_in_K₁)]
  have aux₂ : ∀ x ∈ K₂, 1 ≤ (g₂ * f) x := by
    intro x x_in_K₂
    simp [hg₂ x_in_K₂, hf x (mem_union_right _ x_in_K₂)]
  exact add_le_add (rieszContentAux_le Λ aux₁) (rieszContentAux_le Λ aux₂)

end RieszContentAdditive

section RieszContentRegular

variable [T2Space X] [LocallyCompactSpace X]

/-- The content induced by the linear functional `Λ`. -/
noncomputable def rieszContent (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : Content X where
  toFun := rieszContentAux Λ
  mono' := fun _ _ ↦ rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ ↦ rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

lemma rieszContent_neq_top {K : Compacts X} : rieszContent Λ K ≠ ⊤ := by
  simp only [ne_eq, ENNReal.coe_ne_top, not_false_eq_true]

lemma rieszContentRegular : (rieszContent Λ).ContentRegular := by
  intro K
  simp only [rieszContent]
  apply le_antisymm
  · apply le_iInf
    simp only [le_iInf_iff, ENNReal.coe_le_coe]
    intro K' hK'
    exact rieszContentAux_mono Λ (Set.Subset.trans hK' interior_subset)
  · rw [iInf_le_iff]
    intro b hb
    rw [rieszContentAux, ENNReal.le_coe_iff]
    have : b < ⊤ := by
      obtain ⟨F, hF⟩ := exists_compact_superset K.2
      exact lt_of_le_of_lt (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2) ENNReal.coe_lt_top
    use b.toNNReal
    refine ⟨Eq.symm (ENNReal.coe_toNNReal (ne_of_lt this)), ?_⟩
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_le_coe, ← NNReal.coe_le_coe]
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    set εnn : ℝ≥0 := ⟨ε, le_of_lt hε⟩
    have εnneq : ε.toNNReal = εnn := Real.toNNReal_of_nonneg (le_of_lt hε)
    rw [← NNReal.coe_mk ε (le_of_lt hε), ← NNReal.coe_add, NNReal.coe_le_coe]
    obtain ⟨f, hfleoneonK, hfle⟩ := exists_lt_rieszContentAux_add_pos Λ K (Real.toNNReal_pos.mpr hε)
    rw [rieszContentAux, εnneq] at hfle
    apply le_of_lt (lt_of_le_of_lt _ hfle)
    rw [← NNReal.coe_le_coe]
    apply (le_iff_forall_one_lt_le_mul₀ _).mpr
    · intro α hα
      have : (Λ f) * α = Λ (α.toNNReal • f) := by
        simp only [map_smul, smul_eq_mul, NNReal.coe_mul, Real.coe_toNNReal',
          max_eq_left <| le_of_lt (lt_of_le_of_lt zero_le_one hα)]
        exact mul_comm _ _
      rw [this]
      set K' := f ⁻¹' (Ici α⁻¹.toNNReal) with hK'
      have hKK' : K.carrier ⊆ interior K' := by
        rw [subset_interior_iff]
        use f ⁻¹' (Ioi α⁻¹.toNNReal)
        refine ⟨IsOpen.preimage f.1.2 isOpen_Ioi, ?_, ?_⟩
        · intro x hx
          rw [Set.mem_preimage, Set.mem_Ioi]
          exact lt_of_lt_of_le (Real.toNNReal_lt_one.mpr (inv_lt_one_of_one_lt₀ hα))
            (hfleoneonK x hx)
        · rw [hK']
          intro x hx
          simp only [mem_preimage, mem_Ioi] at hx
          simp only [mem_preimage, mem_Ici]
          exact le_of_lt hx
      have hK'cp : IsCompact K' := by
        apply IsCompact.of_isClosed_subset f.2
        · exact IsClosed.preimage f.1.2 isClosed_Ici
        · rw [hK']
          apply Set.Subset.trans _ subset_closure
          intro x hx
          simp only [mem_preimage, mem_Ici] at hx
          simp only [mem_support]
          apply ne_of_gt
          rw [Real.toNNReal_inv] at hx
          exact (lt_of_lt_of_le
            (inv_pos_of_pos (lt_trans zero_lt_one (Real.one_lt_toNNReal.mpr hα))) hx)
      set hb' := hb ⟨K', hK'cp⟩
      simp only [Compacts.coe_mk, le_iInf_iff] at hb'
      have hbK' : b ≤ rieszContent Λ ⟨K', hK'cp⟩ := hb' hKK'
      rw [ENNReal.le_coe_iff] at hbK'
      obtain ⟨p, hp⟩ := hbK'
      simp only [hp.1, ENNReal.toNNReal_coe, NNReal.val_eq_coe, map_smul, smul_eq_mul,
        NNReal.coe_mul, Real.coe_toNNReal', ge_iff_le]
      apply le_trans (NNReal.GCongr.toReal_le_toReal hp.2)
      simp only [rieszContent]
      rw [rieszContentAux, ← Real.coe_toNNReal (α ⊔ 0) (le_max_right α 0), ← NNReal.coe_mul,
        NNReal.coe_le_coe]
      apply csInf_le
      · simp only [OrderBot.bddBelow]
      · simp only [mem_image, mem_setOf_eq]
        use α.toNNReal • f
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
            ← NNReal.coe_le_coe, NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal']
          rw [← (left_eq_sup.mpr <| le_of_lt (lt_of_le_of_lt zero_le_one hα)), mul_comm]
          apply (inv_le_iff_one_le_mul₀ (lt_trans zero_lt_one hα)).mp
          rw [← Set.mem_Ici]
          simp only [mem_Ici, ge_iff_le]
          exact Real.toNNReal_le_iff_le_coe.mp hx
        · simp only [map_smul, smul_eq_mul, mul_eq_mul_right_iff]
          left
          rw [Real.toNNReal_eq_toNNReal_iff (le_of_lt (lt_of_le_of_lt zero_le_one hα))
            (le_max_right α 0), left_eq_sup]
          exact le_of_lt (lt_of_le_of_lt zero_le_one hα)
    · exact zero_le (Λ f)

end RieszContentRegular

section RieszMeasure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `rieszContent` is promoted to a measure. -/
def μ := (MeasureTheory.Content.measure (rieszContent Λ))

lemma leRieszMeasure_Compacts {f : C_c(X, ℝ≥0)} (hf : ∀ (x : X), f x ≤ 1) {K : Compacts X}
    (h : tsupport f ⊆ K) : ENNReal.ofReal (Λ f) ≤ (μ Λ) K := by
  simp only [μ, MeasureTheory.Content.measure_eq_content_of_regular (rieszContent Λ)
    (rieszContentRegular Λ)]
  simp only [rieszContent, ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ K hε
  apply le_of_lt (lt_of_le_of_lt _ hg.2)
  apply Λ_mono Λ
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x) (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    exact zero_le (g x)

lemma leRieszMeasure_Opens {f : C_c(X, ℝ≥0)} (hf : ∀ (x : X), f x ≤ 1) {V : Opens X}
    (h : tsupport f ⊆ V) :
    ENNReal.ofReal (Λ f) ≤ (μ Λ) V := by
  apply le_trans _ (MeasureTheory.measure_mono h)
  rw [← TopologicalSpace.Compacts.coe_mk (tsupport f) f.2]
  apply leRieszMeasure_Compacts Λ hf
  simp only [Compacts.coe_mk]
  exact subset_rfl

end RieszMeasure

section RieszMarkovKakutani

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

variable (f : C(X, ℝ≥0∞))
#check ∫⁻ (x : X), f x ∂(μ Λ)

/-- The Riesz-Markov-Kakutani theorem. -/
theorem RMK [Nonempty X] : ∀ (f : C_c(X, ℝ≥0)), ∫⁻ (x : X), f x ∂(μ Λ) = Λ f := by
  intro f
  have RMK_le : ∀ (f : C_c(X, ℝ≥0)), Λ f ≤ ∫⁻ (x : X), f x ∂(μ Λ) := by
    intro f
    set L := Set.range f with hLdef
    have hL : IsCompact L := by exact HasCompactSupport.isCompact_range f.2 f.1.2
    have hLNonempty : Nonempty L := instNonemptyRange f
    have BddBelow_bbdAbove_L := isBounded_iff_bddBelow_bddAbove.mp
      (Metric.isCompact_iff_isClosed_bounded.mp hL).2
    obtain ⟨a, ha⟩ := BddBelow_bbdAbove_L.1
    obtain ⟨b, hb⟩ := BddBelow_bbdAbove_L.2
    have hafx : ∀ (x : X), a ≤ f x := by
      intro x
      apply ha
      rw [hLdef]
      simp only [mem_range, exists_apply_eq_apply]
    have hfxb : ∀ (x : X), f x ≤ b:= by
      intro x
      apply hb
      rw [hLdef]
      simp only [mem_range, exists_apply_eq_apply]
    have hab : a ≤ b := by
      obtain ⟨c, hc⟩ := hLNonempty
      exact le_trans (mem_lowerBounds.mp ha c hc) (mem_upperBounds.mp hb c hc)
    sorry
  sorry
  --   -- have habnonneg : 0 ≤ |a| + b := by
  --   --   apply le_trans _ (add_le_add_right (neg_le_abs a) b)
  --   --   simp only [le_neg_add_iff_add_le, add_zero]
  --   --   exact hab
  --   apply le_iff_forall_pos_le_add.mpr
  --   intro ε hε
  --   have hltε : ∃ (ε' : ℝ), 0 < ε' ∧
  --       ε' * (2 * ((μ Λ hΛ) (tsupport f)).toReal + |a| + b + ε') < ε := by
  --     set A := 2 * ((μ Λ hΛ) (tsupport f)).toReal + |a| + b with hA
  --     use ε / (4 * A + 2 + 2 * ε)
  --     have hAnonneg : 0 ≤ A := by
  --       rw [hA, add_assoc]
  --       apply add_nonneg _ habnonneg
  --       simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, toReal_nonneg]
  --     constructor
  --     · apply div_pos hε
  --       linarith
  --     · rw [left_distrib]
  --       have h1 : ε / (4 * A + 2 + 2 * ε) * A < ε / 2 := by
  --         rw [← mul_div_right_comm, mul_div_assoc]
  --         nth_rw 3 [← mul_one ε]
  --         rw [mul_div_assoc]
  --         apply mul_lt_mul_of_pos_left _ hε
  --         apply (div_lt_div_iff _ two_pos).mpr
  --         · linarith
  --         · linarith
  --       have h2 : ε / (4 * A + 2 + 2 * ε) < ε / 2 := by
  --         apply div_lt_div_of_pos_left hε two_pos
  --         linarith
  --       have h3 : 0 < 4 * A + 2 + 2 * ε := by
  --         linarith
  --       have h4 : ε / (4 * A + 2 + 2 * ε) * (ε / (4 * A + 2 + 2 * ε)) < ε / 2 := by
  --         rw [_root_.lt_div_iff two_pos, mul_comm, ← mul_div_assoc, ← mul_div_assoc, div_lt_iff h3,
  --           ← mul_assoc, mul_comm, ← mul_assoc, ← mul_div_assoc, div_lt_iff h3, mul_assoc,
  --           mul_assoc]
  --         apply mul_lt_mul_of_pos_left _ hε
  --         have h41 : 2 < 4 * A + 2 + 2 * ε := by
  --           linarith
  --         have h42 : ε < 4 * A + 2 + 2 * ε := by
  --           linarith
  --         exact mul_lt_mul h41 (le_of_lt h42) hε (le_of_lt h3)
  --       nth_rw 7 [← add_halves' ε]
  --       exact add_lt_add h1 h4
  --   obtain ⟨ε', hε'⟩ := hltε
  --   apply le_of_lt (lt_of_le_of_lt _ (add_lt_add_left hε'.2 _))
  --   set δ := ε' / 2 with hδ
  --   have hδpos : 0 < δ := by
  --     rw [hδ]
  --     exact div_pos hε'.1 two_pos
  --   set N := (b - a) / δ with hN
  --   have hNNonneg : 0 ≤ N :=
  --     by exact div_nonneg (sub_nonneg.mpr hab) (le_of_lt hδpos)
  --   set y : ℤ → ℝ := fun n => b + δ * (n - (⌈N⌉₊+1)) with hy
  --   have ymono : ∀ (j k : ℤ), y j < y k → j < k := by
  --     intro j k
  --     rw [hy]
  --     simp only [add_lt_add_iff_left]
  --     intro h
  --     apply (@Int.cast_lt ℝ).mp
  --     apply @lt_of_tsub_lt_tsub_right ℝ j k (⌈N⌉₊ + 1)
  --     exact lt_of_mul_lt_mul_left h (le_of_lt hδpos)
  --   have hy1leyn : ∀ (n : Fin (⌈N⌉₊ + 1)), y 1 ≤ y (n + 1) := by
  --     intro n
  --     rw [hy]
  --     simp only [Int.cast_one, sub_add_cancel_right, mul_neg, Int.cast_add, Int.cast_natCast,
  --       add_sub_add_right_eq_sub, add_lt_add_iff_left]
  --     rw [_root_.mul_sub]
  --     apply le_add_neg_iff_le.mp
  --     ring_nf
  --     simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right]
  --     exact mul_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _)
  --   have hymono' : ∀ (m n : Fin (⌈N⌉₊ + 1)), m ≤ n → y m ≤ y n := by
  --     intro m n hmn
  --     rw [hy]
  --     simp only [Int.cast_natCast, add_le_add_iff_left]
  --     rw [_root_.mul_sub, _root_.mul_sub]
  --     simp only [tsub_le_iff_right, sub_add_cancel]
  --     apply mul_le_mul_of_nonneg_left _ (le_of_lt hδpos)
  --     rw [Nat.cast_le]
  --     simp only [Fin.val_fin_le]
  --     exact hmn
  --   have hy0 : y 0 < a := by
  --     rw [hy, hN]
  --     simp only [Int.cast_zero, Int.ceil_add_one, Int.cast_add, Int.cast_one, zero_sub, neg_add_rev]
  --     apply lt_tsub_iff_left.mp
  --     apply (lt_div_iff' hδpos).mp
  --     simp only [add_neg_lt_iff_lt_add]
  --     rw [neg_lt_iff_pos_add, add_assoc, ← neg_lt_iff_pos_add']
  --     apply lt_add_of_lt_add_right _ (Nat.le_ceil _)
  --     rw [neg_lt_iff_pos_add]
  --     apply pos_of_mul_pos_left _ (le_of_lt hδpos)
  --     rw [add_mul, add_mul, div_mul, div_mul, div_self (Ne.symm (ne_of_lt hδpos))]
  --     simp only [div_one, one_mul]
  --     linarith

  --   set E : ℤ → Set X := fun n => (f ⁻¹' Ioc (y n) (y (n+1))) ∩ (tsupport f) with hE
  --   set Erest : Fin (⌈N⌉₊ + 1) → Set X := fun n => E n with hErest
  --   have hErestdisjoint : PairwiseDisjoint univ Erest := by
  --     intro m _ n _ hmn
  --     apply Disjoint.preimage
  --     simp only [mem_preimage]
  --     by_cases hmltn : m < n
  --     · rw [Set.disjoint_left]
  --       intro x hx
  --       simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
  --       simp only [mem_Ioc, mem_setOf_eq] at hx
  --       left
  --       left
  --       apply le_trans hx.1.2
  --       have : m.1 + (1 : ℤ) = (m+1 : Fin (⌈N⌉₊ + 1)) := by
  --         rw [← Nat.cast_add_one, Nat.cast_inj]
  --         apply Eq.symm (Fin.val_add_one_of_lt _)
  --         exact lt_of_lt_of_le hmltn (Fin.le_last n)
  --       rw [this]
  --       apply hymono' _ _
  --       exact Fin.add_one_le_of_lt hmltn
  --     · rw [Set.disjoint_left]
  --       intro x hx
  --       simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
  --       simp only [mem_Ioc, mem_setOf_eq] at hx
  --       push_neg at hmltn
  --       set hnltm := lt_of_le_of_ne hmltn (Ne.symm hmn)
  --       left
  --       right
  --       apply lt_of_le_of_lt _ hx.1.1
  --       have : n.1 + (1 : ℤ) = (n+1 : Fin (⌈N⌉₊ + 1)) := by
  --         rw [← Nat.cast_add_one, Nat.cast_inj]
  --         apply Eq.symm (Fin.val_add_one_of_lt _)
  --         exact lt_of_lt_of_le hnltm (Fin.le_last m)
  --       rw [this]
  --       apply hymono' _ _
  --       exact Fin.add_one_le_of_lt hnltm
  --   have hErestdisjoint' : Pairwise (Disjoint on Erest) := by
  --     intro m n hmn
  --     apply Disjoint.preimage
  --     simp only [mem_preimage]
  --     by_cases hmltn : m < n
  --     · rw [Set.disjoint_left]
  --       intro x hx
  --       simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
  --       simp only [mem_Ioc, mem_setOf_eq] at hx
  --       left
  --       left
  --       apply le_trans hx.1.2
  --       have : m.1 + (1 : ℤ) = (m+1 : Fin (⌈N⌉₊ + 1)) := by
  --         rw [← Nat.cast_add_one, Nat.cast_inj]
  --         apply Eq.symm (Fin.val_add_one_of_lt _)
  --         exact lt_of_lt_of_le hmltn (Fin.le_last n)
  --       rw [this]
  --       apply hymono' _ _
  --       exact Fin.add_one_le_of_lt hmltn
  --     · rw [Set.disjoint_left]
  --       intro x hx
  --       simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
  --       simp only [mem_Ioc, mem_setOf_eq] at hx
  --       push_neg at hmltn
  --       set hnltm := lt_of_le_of_ne hmltn (Ne.symm hmn)
  --       left
  --       right
  --       apply lt_of_le_of_lt _ hx.1.1
  --       have : n.1 + (1 : ℤ) = (n+1 : Fin (⌈N⌉₊ + 1)) := by
  --         rw [← Nat.cast_add_one, Nat.cast_inj]
  --         apply Eq.symm (Fin.val_add_one_of_lt _)
  --         exact lt_of_lt_of_le hnltm (Fin.le_last m)
  --       rw [this]
  --       apply hymono' _ _
  --       exact Fin.add_one_le_of_lt hnltm
  --   have hErestmeasurable : ∀ (n : Fin (⌈N⌉₊ + 1)), MeasurableSet (Erest n) := by
  --     intro n
  --     rw [hErest]
  --     simp only
  --     apply MeasurableSet.inter
  --     · exact (ContinuousMap.measurable f.1) measurableSet_Ioc
  --     · exact measurableSet_closure
  --   have hErestsubtsupport : ∀ (n : Fin (⌈N⌉₊ + 1)), Erest n ⊆ tsupport f := by
  --     intro n
  --     rw [hErest]
  --     simp only
  --     rw [hE]
  --     simp only [inter_subset_right]
  --   have hrangefsubioc: range f ⊆ Ioc (y 0) (y (⌈N⌉₊ + 1)) := by
  --     intro z hz
  --     simp only [mem_Ioc]
  --     constructor
  --     · apply lt_of_lt_of_le hy0
  --       apply ha
  --       rw [hLdef]
  --       exact hz
  --     · rw [hy]
  --       simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, sub_self, mul_zero, add_zero]
  --       apply hb
  --       rw [hLdef]
  --       exact hz
  --   have hrangefsubiunion: range f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), Ioc (y n) (y (n+1)) := by
  --     have : y = fun (n : ℤ) => b - δ * ⌈N⌉₊ - δ + n • δ := by
  --       ext n
  --       rw [hy]
  --       simp only [zsmul_eq_mul]
  --       ring
  --     have : ⋃ n, Ioc (y n) (y (n+1)) = univ := by
  --       rw [this]
  --       simp only [Int.cast_add, Int.cast_one]
  --       exact iUnion_Ioc_add_zsmul hδpos (b - δ * ⌈N⌉₊ - δ)
  --     intro z hz
  --     have : z ∈ ⋃ n, Ioc (y n) (y (n+1)) := by
  --       rw [this]
  --       exact trivial
  --     obtain ⟨j, hj⟩ := mem_iUnion.mp this
  --     have hjnonneg : 0 ≤ j := by
  --       apply (Int.add_le_add_iff_right 1).mp
  --       apply Int.le_of_sub_one_lt
  --       simp only [zero_add, sub_self]
  --       apply ymono
  --       apply lt_of_lt_of_le hy0
  --       simp only [mem_Ioc] at hj
  --       apply le_trans _ hj.2
  --       apply ha
  --       rw [hLdef]
  --       exact hz
  --     have hjltceil : j < ⌈N⌉₊ + 1 := by
  --       apply ymono
  --       simp only [mem_Ioc] at hj
  --       apply lt_of_lt_of_le hj.1 _
  --       rw [hy]
  --       simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, sub_self, mul_zero, add_zero]
  --       apply hb
  --       rw [hLdef]
  --       exact hz
  --     have hnltceil : j.toNat < ⌈N⌉₊ + 1 := by
  --       exact (Int.toNat_lt hjnonneg).mpr hjltceil
  --     rw [mem_iUnion]
  --     use ⟨j.toNat, hnltceil⟩
  --     simp only
  --     rw [Int.toNat_of_nonneg hjnonneg]
  --     exact hj
  --   have htsupportsubErest : tsupport f ⊆ ⋃ j, Erest j := by
  --     intro x hx
  --     rw [hErest, hE]
  --     simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_and_right]
  --     obtain ⟨j, hj⟩ := mem_iUnion.mp (Set.mem_of_subset_of_mem hrangefsubiunion
  --       (Set.mem_range_self x))
  --     constructor
  --     · use j
  --     · exact hx
  --   have htsupporteqErest : tsupport f = ⋃ j, Erest j := by
  --     apply subset_antisymm
  --     · exact htsupportsubErest
  --     · exact Set.iUnion_subset hErestsubtsupport
  --   have hμsuppfeqμErest : (μ Λ hΛ) (tsupport f) = ∑ n, (μ Λ hΛ) (Erest n) := by
  --     rw [htsupporteqErest]
  --     rw [← MeasureTheory.measure_biUnion_finset]
  --     · simp only [Finset.mem_univ, iUnion_true]
  --     · simp only [Finset.coe_univ]
  --       exact hErestdisjoint
  --     · intro n _
  --       exact hErestmeasurable n
  --   set SpecV := fun (n : Fin (⌈N⌉₊ + 1)) =>
  --     MeasureTheory.Content.outerMeasure_exists_open (rieszContent Λ hΛ)
  --     (ne_of_lt (lt_of_le_of_lt ((rieszContent Λ hΛ).outerMeasure.mono (hErestsubtsupport n))
  --     (MeasureTheory.Content.outerMeasure_lt_top_of_isCompact (rieszContent Λ hΛ) f.2)))
  --     (ne_of_gt (Real.toNNReal_pos.mpr (div_pos hε'.1 (Nat.cast_pos.mpr (Nat.add_one_pos ⌈N⌉₊)))))
  --   set V : Fin (⌈N⌉₊ + 1) → Opens X := fun n => Classical.choose (SpecV n) ⊓
  --     ⟨(f ⁻¹' Iio (y (n + 1) + ε')), IsOpen.preimage f.1.2 isOpen_Iio⟩ with hV
  --   have hErestsubV : ∀ (n : Fin (⌈N⌉₊ + 1)), Erest n ⊆ V n := by
  --     intro n
  --     rw [hV]
  --     simp only [Nat.cast_succ, Opens.coe_inf, Opens.coe_mk, subset_inter_iff]
  --     constructor
  --     · simp only [Nat.cast_add, Nat.cast_one] at SpecV
  --       exact (Classical.choose_spec (SpecV n)).1
  --     · rw [hErest]
  --       simp only
  --       apply Set.Subset.trans (Set.inter_subset_left) _
  --       intro z hz
  --       rw [Set.mem_preimage]
  --       rw [Set.mem_preimage] at hz
  --       exact lt_of_le_of_lt hz.2 (lt_add_of_pos_right (y (n + 1)) hε'.1)
  --   have htsupportsubV : tsupport f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), V n := by
  --     apply Set.Subset.trans htsupportsubErest _
  --     apply Set.iUnion_mono
  --     exact hErestsubV
  --   obtain ⟨g, hg⟩ := exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed
  --     (fun n => (V n).2) f.2 htsupportsubV
  --   have hf : f = ∑ n, g n • f := by
  --     ext x
  --     simp only [CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_smulc,
  --       smul_eq_mul, Finset.sum_apply]
  --     rw [← Finset.sum_mul, ← Finset.sum_apply]
  --     by_cases hx : x ∈ tsupport f
  --     · rw [hg.2.2.1 hx]
  --       simp only [Pi.one_apply, one_mul]
  --     · rw [image_eq_zero_of_nmem_tsupport hx]
  --       simp only [Finset.sum_apply, mul_zero]
  --   have μtsupportflesumΛgn :
  --       (μ Λ hΛ (TopologicalSpace.Compacts.mk (tsupport f) f.2)) ≤
  --       ENNReal.ofReal (Λ (∑ n, ⟨g n, hg.2.1 n⟩)) := by
  --     rw [μ]
  --     rw [MeasureTheory.Content.measure_eq_content_of_regular (rieszContent Λ hΛ)
  --       (rieszContentRegular Λ hΛ) ⟨tsupport f, f.2⟩]
  --     rw [rieszContent]
  --     simp only [map_sum]
  --     apply ENNReal.coe_le_iff.mpr
  --     intro p hp
  --     rw [← ENNReal.ofReal_coe_nnreal] at hp
  --     rw [ENNReal.ofReal_eq_ofReal_iff] at hp
  --     rw [rieszContentNonneg]
  --     apply csInf_le (rieszContentNonneg_image_BddBelow Λ hΛ ⟨tsupport f, f.2⟩)
  --     rw [Set.mem_image]
  --     -- need to define g n as C(X, ℝ≥0)
  --     set nng : Fin (⌈N⌉₊ + 1) → C_c(X, ℝ≥0) :=
  --       fun n => ⟨⟨Real.toNNReal ∘ (g n), Continuous.comp continuous_real_toNNReal (g n).2⟩,
  --       @HasCompactSupport.comp_left _ _ _ _ _ _ Real.toNNReal (g n) (hg.2.1 n) Real.toNNReal_zero⟩
  --       with hnng
  --     use ∑ n, nng n
  --     constructor
  --     · intro x hx
  --       rw [CompactlySupportedContinuousMap.sum_apply Finset.univ (fun n => nng n) x]
  --       rw [hnng]
  --       simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply]
  --       rw [← Real.toNNReal_sum_of_nonneg _]
  --       · simp only [Real.one_le_toNNReal]
  --         set hgx := hg.2.2.1 hx
  --         simp only [Finset.sum_apply, Pi.one_apply] at hgx
  --         rw [hgx]
  --       · intro n _
  --         exact (hg.2.2.2 n x).1
  --     · rw [RestrictNonneg]
  --       rw [NNReal.eq_iff]
  --       simp only [coe_mk]
  --       rw [continuousExtendToReal_sum, map_sum Λ _ Finset.univ, ← hp]
  --       apply Finset.sum_congr (Eq.refl _)
  --       intro n _
  --       rw [hnng, continuousExtendToReal]
  --       simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
  --       apply congr (Eq.refl _)
  --       simp only [CompactlySupportedContinuousMap.mk.injEq]
  --       ext x
  --       simp only [ContinuousMap.coe_mk, comp_apply, Real.coe_toNNReal', max_eq_left_iff]
  --       exact (hg.2.2.2 n x).1
  --     · rw [← map_sum Λ _ Finset.univ]
  --       apply hΛ
  --       intro x
  --       simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
  --         CompactlySupportedContinuousMap.coe_toContinuousMap,
  --         CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
  --         Finset.sum_apply]
  --       apply Finset.sum_nonneg
  --       intro n hn
  --       exact (hg.2.2.2 n x).1
  --     · exact p.2
  --   have μtsupportflesumΛgn' : (μ Λ hΛ (TopologicalSpace.Compacts.mk (tsupport f) f.2)).toReal ≤
  --       ∑ n, Λ ⟨g n, hg.2.1 n⟩ := by
  --     rw [← map_sum]
  --     apply ENNReal.toReal_le_of_le_ofReal _ μtsupportflesumΛgn
  --     apply hΛ
  --     intro x
  --     simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
  --       CompactlySupportedContinuousMap.coe_toContinuousMap,
  --       CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
  --       Finset.sum_apply]
  --     apply Finset.sum_nonneg
  --     intro n _
  --     exact (hg.2.2.2 n x).1
  --   have hErestx : ∀ (n : Fin (⌈N⌉₊ + 1)), ∀ (x : X), x ∈ Erest n → y n < f x := by
  --     intro n x hnx
  --     rw [hErest, hE] at hnx
  --     simp only [mem_inter_iff, mem_preimage, mem_Ioc] at hnx
  --     exact hnx.1.1
  --   have hgf : ∀ (n : Fin (⌈N⌉₊ + 1)), (g n • f).1 ≤ ((y (n + 1) + ε') • (⟨g n, hg.2.1 n⟩ : C_c(X, ℝ))).1 := by
  --     intro n x
  --     simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap,
  --       CompactlySupportedContinuousMap.smulc_apply, CompactlySupportedContinuousMap.coe_smul,
  --       CompactlySupportedContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul]
  --     by_cases hx : x ∈ tsupport (g n)
  --     · rw [mul_comm]
  --       apply mul_le_mul_of_nonneg_right _ (hg.2.2.2 n x).1
  --       have : x ∈ V n := Set.mem_of_subset_of_mem (hg.1 n) hx
  --       rw [hV] at this
  --       simp only [Nat.cast_add, Nat.cast_one] at this
  --       rw [TopologicalSpace.Opens.mem_mk] at this
  --       simp only [Opens.carrier_eq_coe, Opens.coe_inf, Opens.coe_mk, mem_inter_iff,
  --         SetLike.mem_coe, mem_preimage, mem_Iio] at this
  --       exact le_of_lt this.2
  --     · rw [image_eq_zero_of_nmem_tsupport hx]
  --       simp only [zero_mul, mul_zero, le_refl]
  --   have hΛgf : ∀ (n : Fin (⌈N⌉₊ + 1)), n ∈ Finset.univ →  Λ (g n • f)
  --       ≤ Λ ((y (n + 1) + ε') • (⟨g n, hg.2.1 n⟩ : C_c(X, ℝ))) := by
  --     intro n _
  --     exact Λ_mono Λ hΛ (hgf n)
  --   nth_rw 1 [hf]
  --   simp only [map_sum, CompactlySupportedContinuousMap.coe_sum,
  --     Finset.sum_apply, Pi.mul_apply]
  --   apply le_trans (Finset.sum_le_sum hΛgf)
  --   simp only [map_smul, smul_eq_mul]
  --   rw [← add_zero ε']
  --   simp_rw [← add_assoc, ← sub_self |a|, ← add_sub_assoc, _root_.sub_mul]
  --   simp only [Finset.sum_sub_distrib]
  --   rw [← Finset.mul_sum]
  --   have hy1a : 0 < y 1 + ε' + |a| := by
  --     rw [hy]
  --     simp only [Fin.val_zero, CharP.cast_eq_zero, zero_add, Int.cast_one, sub_add_cancel_right,
  --       mul_neg]
  --     rw [add_assoc, add_assoc, add_comm, add_assoc, lt_neg_add_iff_lt, ← lt_div_iff' hδpos]
  --     apply lt_trans (Nat.ceil_lt_add_one hNNonneg)
  --     rw [lt_div_iff' hδpos, hN, mul_add, mul_comm, div_mul, div_self (ne_of_gt hδpos)]
  --     simp only [div_one, mul_one]
  --     rw [hδ]
  --     apply lt_add_of_tsub_lt_right
  --     rw [add_sub_assoc, add_comm, ← add_sub_assoc]
  --     apply sub_right_lt_of_lt_add
  --     rw [sub_add]
  --     simp only [sub_self, sub_zero]
  --     apply lt_neg_add_iff_lt.mp
  --     rw [add_assoc, ← add_assoc]
  --     apply add_pos_of_pos_of_nonneg
  --     · simp only [lt_neg_add_iff_add_lt, add_zero, half_lt_self_iff]
  --       exact hε'.1
  --     · exact neg_le_iff_add_nonneg'.mp (neg_abs_le a)
  --   have hyna : ∀ (n : Fin (⌈N⌉₊ + 1)), 0 < y (n + 1) + ε' + |a| := by
  --     intro n
  --     by_cases hn : n = 0
  --     · rw [hn]
  --       exact hy1a
  --     · push_neg at hn
  --       have hnp : 0 < n := by
  --         exact Fin.pos_iff_ne_zero.mpr hn
  --       rw [← sub_add_cancel (y (n + 1)) (y 1), add_assoc, add_assoc]
  --       apply add_pos_of_nonneg_of_pos
  --       · exact sub_nonneg_of_le (hy1leyn n)
  --       · rw [← add_assoc]
  --         exact hy1a
  --   have hΛgnleμVn : ∀ (n : Fin (⌈N⌉₊ + 1)),
  --       ENNReal.ofReal (Λ (⟨g n, hg.2.1 n⟩)) ≤ (μ Λ hΛ) (V n) := by
  --     intro n
  --     apply leRieszMeasure_isOpen
  --     · simp only [CompactlySupportedContinuousMap.coe_mk]
  --       intro x
  --       exact hg.2.2.2 n x
  --     · simp only [CompactlySupportedContinuousMap.coe_mk]
  --       rw [← TopologicalSpace.Opens.carrier_eq_coe]
  --       exact hg.1 n

  --   have hμVnleμEnaddε : ∀ (n : Fin (⌈N⌉₊ + 1)),
  --       (μ Λ hΛ) (V n) ≤ (μ Λ hΛ) (Erest n) + ENNReal.ofReal (ε' / ((⌈N⌉₊ + 1 : ℕ))) := by
  --     intro n
  --     rw [μ]
  --     rw [← TopologicalSpace.Opens.carrier_eq_coe]
  --     rw [MeasureTheory.Content.measure_apply (rieszContent Λ hΛ) (V n).2.measurableSet]
  --     rw [TopologicalSpace.Opens.carrier_eq_coe]
  --     rw [MeasureTheory.Content.measure_apply (rieszContent Λ hΛ) (hErestmeasurable n)]
  --     set Un := Classical.choose (SpecV n) with hUn
  --     set SpecUn := Classical.choose_spec (SpecV n)
  --     have hVU : V n ≤ Un := by
  --       exact inf_le_left
  --     have hμVleμU :
  --         (rieszContent Λ hΛ).outerMeasure (V n) ≤ (rieszContent Λ hΛ).outerMeasure (Un) := by
  --       exact MeasureTheory.OuterMeasure.mono (rieszContent Λ hΛ).outerMeasure hVU
  --     apply le_trans hμVleμU
  --     rw [hUn]
  --     have hENNNR : ∀ (p : ℝ), ENNReal.ofReal p = p.toNNReal := by
  --       intro p
  --       rfl
  --     rw [hENNNR]
  --     exact SpecUn.2
  --   have hμErestlttop : ∀ (n : Fin (⌈N⌉₊ + 1)), (μ Λ hΛ) (Erest n) < ⊤ := by
  --     intro n
  --     apply lt_of_le_of_lt (MeasureTheory.measure_mono (hErestsubtsupport n))
  --     have : f = f.toFun := by
  --       exact rfl
  --     rw [μ, this,
  --       MeasureTheory.Content.measure_apply _ f.2.measurableSet]
  --     exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
  --   have hμsuppfeqμErest' : ((μ Λ hΛ) (tsupport f)).toReal = ∑ n, ((μ Λ hΛ) (Erest n)).toReal := by
  --     rw [← ENNReal.toReal_sum]
  --     exact congr rfl hμsuppfeqμErest
  --     intro n _
  --     rw [← lt_top_iff_ne_top]
  --     exact hμErestlttop n
  --   have hΛgnleμVn' : ∀ (n : Fin (⌈N⌉₊ + 1)),
  --       Λ (⟨g n, hg.2.1 n⟩) ≤ ((μ Λ hΛ) (V n)).toReal := by
  --     intro n
  --     apply (ENNReal.ofReal_le_iff_le_toReal _).mp (hΛgnleμVn n)
  --     rw [← lt_top_iff_ne_top]
  --     apply lt_of_le_of_lt (hμVnleμEnaddε n)
  --     rw [WithTop.add_lt_top]
  --     constructor
  --     · exact hμErestlttop n
  --     · exact ENNReal.ofReal_lt_top
  --   have hμVnleμEnaddε' : ∀ (n : Fin (⌈N⌉₊ + 1)),
  --       ((μ Λ hΛ) (V n)).toReal ≤ ((μ Λ hΛ) (Erest n)).toReal + (ε' / ((⌈N⌉₊ + 1 : ℕ))) := by
  --     intro n
  --     rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
  --     apply ENNReal.toReal_le_add (hμVnleμEnaddε n)
  --     · exact lt_top_iff_ne_top.mp (hμErestlttop n)
  --     · exact ENNReal.ofReal_ne_top
  --   have ynsubεmulμEnleintEnf :
  --       ∀ (n : Fin (⌈N⌉₊ + 1)), (y (n + 1) - ε') * ((μ Λ hΛ) (Erest n)).toReal
  --       ≤ ∫ x in (Erest n), f x ∂(μ Λ hΛ) := by
  --     intro n
  --     apply MeasureTheory.setIntegral_ge_of_const_le (hErestmeasurable n)
  --     · rw [μ]
  --       rw [MeasureTheory.Content.measure_apply _ (hErestmeasurable n)]
  --       rw [← lt_top_iff_ne_top]
  --       apply lt_of_le_of_lt (MeasureTheory.OuterMeasure.mono _ (hErestsubtsupport n))
  --       exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
  --     · intro x hx
  --       apply le_of_lt (lt_trans _ (hErestx n x hx))
  --       rw [hy]
  --       simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_add_right_eq_sub]
  --       rw [sub_add_eq_sub_sub]
  --       nth_rw 2 [_root_.mul_sub]
  --       rw [add_sub_assoc]
  --       simp only [mul_one, add_lt_add_iff_left, sub_lt_sub_iff_left]
  --       rw [hδ]
  --       linarith



  --     · apply MeasureTheory.Integrable.integrableOn
  --       rw [μ]
  --       exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
  --   apply le_trans (tsub_le_tsub_left (mul_le_mul_of_nonneg_left μtsupportflesumΛgn' (abs_nonneg a)) _)
  --   rw [add_mul]
  --   simp only [add_sub_cancel_right]
  --   apply le_trans (tsub_le_tsub_right (Finset.sum_le_sum (fun n => (fun _ =>
  --     mul_le_mul_of_nonneg_left
  --     (le_trans (hΛgnleμVn' n) (hμVnleμEnaddε' n)) (le_of_lt (hyna n))))) _)
  --   simp_rw [mul_add _ ((μ Λ hΛ) _).toReal _]
  --   rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  --   nth_rw 1 [← sub_add_cancel ε' ε']
  --   simp_rw [add_assoc _ _ |a|, ← add_assoc _ _ (ε' + |a|), Eq.symm (add_comm_sub _ ε' ε'),
  --     add_assoc _ ε' _, ← add_assoc ε' ε' |a|, Eq.symm (two_mul ε')]
  --   simp_rw [add_mul _ (2 * ε' + |a|) ((μ Λ hΛ) _).toReal]
  --   rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hμsuppfeqμErest', add_mul (2 * ε') |a| _]
  --   simp only [Compacts.coe_mk]
  --   have hynleb : ∀ (n : Fin (⌈N⌉₊ + 1)), y (n + 1) ≤ b := by
  --     intro n
  --     rw [hy]
  --     simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_add_right_eq_sub,
  --       add_le_iff_nonpos_right]
  --     apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hδpos)
  --     simp only [tsub_le_iff_right, zero_add, Nat.cast_le]
  --     exact Fin.is_le n
  --   have hynleb' : ∀ (n : Fin (⌈N⌉₊ + 1)), y (n + 1) + (ε' + |a|) ≤ |a| + b + ε':= by
  --     intro n
  --     set h := hynleb n
  --     linarith
  --   rw [add_assoc, add_sub_assoc, add_sub_assoc, add_add_sub_cancel, ← add_assoc]
  --   apply le_trans ((add_le_add_iff_left _).mpr (mul_le_mul_of_nonneg_right
  --     (Finset.sum_le_sum (fun n => fun _ => hynleb' n))
  --     (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))))
  --   simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
  --     Nat.cast_one]
  --   rw [mul_comm _ (|a| + b + ε'), mul_assoc (|a| + b + ε') _ _, ← mul_div_assoc]
  --   nth_rw 2 [mul_comm _ ε']
  --   rw [mul_div_assoc, div_self (ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) one_pos)),
  --     mul_one]
  --   rw [MeasureTheory.integral_tsupport, htsupporteqErest]
  --   nth_rw 3 [μ]
  --   have : f = f.toFun := by rfl
  --   rw [this]
  --   rw [MeasureTheory.integral_fintype_iUnion hErestmeasurable hErestdisjoint'
  --     fun n =>
  --     (MeasureTheory.Integrable.integrableOn (Continuous.integrable_of_hasCompactSupport f.1.2 f.2))]
  --   rw [add_assoc]
  --   apply add_le_add
  --   · apply Finset.sum_le_sum
  --     exact fun n => fun _ => ynsubεmulμEnleintEnf n
  --   · linarith
  -- apply le_antisymm
  -- · calc ∫ (x : X), f x ∂(μ Λ hΛ) = ∫ (x : X), -(-f) x ∂(μ Λ hΛ) := by simp only
  --     [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_neg]
  --   _ = - ∫ (x : X), (-f) x ∂(μ Λ hΛ) := by exact MeasureTheory.integral_neg' (-f)
  --   _ ≤ - Λ (-f) := by exact neg_le_neg (RMK_le (-f))
  --   _ = Λ (- -f) := by exact Eq.symm (Λ_neg Λ)
  --   _ = Λ f := by simp only [neg_neg]
  -- · exact RMK_le f

end RieszMarkovKakutani
