/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Caratheodory

/-!
# Carathéodory's convexity theorem for convex cones

In this file we prove Carathéodory's convexity theorem for convex cones. Carathéodory's theorem
states that if `x` is in the convex cone generated by a set `s`, then `x` is a convex combination
of linearly independent elements of `s`. This is the replacement of the usual statement of vector
spaces having bases for the setting of convex cones.

The proof follows the proof of Carathéodory's theorem for convex hulls closely.


## Main results

- `toPointedCone_eq_union`: Carathéodory's convexity theorem for convex cones.
- `mem_toPointedCone_iff_eq_pos_convex_span`: A more explicit version of `toPointedCone_eq_union`.

-/


universe u

open Set Finset

open BigOperators

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

namespace Caratheodory

/-- If `x` is in the cone of some finset `t` whose elements are not linearly-independent,
then it is in the cone of a strict subset of `t`. -/
theorem mem_toPointedCone_erase [DecidableEq E] {t : Finset E}
    (h : ¬LinearIndependent 𝕜 ((↑) : t → E)) {x : E} (hx : x ∈ Set.toPointedCone 𝕜 t) :
    ∃ y : (↑t : Set E), x ∈ (↑(t.erase y) : Set E).toPointedCone 𝕜 := by
  -- `relation₁: ∑ i in t, f i • i = x`
  replace ⟨f, relation₁⟩ := mem_span_finset.1 hx
  simp only [toPointedCone, mem_span_finset, mem_span_finset, coe_sort_coe, coe_mem,
    not_true_eq_false, Subtype.exists, exists_prop]
  by_cases hf : ∃ i₀, i₀ ∈ t ∧ f i₀ = 0
  · -- Easy case: some `f i₀ = 0`.
    -- In this case, we can erase `i₀`.
    replace ⟨i₀, hi₀t, hf⟩ := hf
    use i₀, hi₀t, f
    rwa [sum_erase_eq_sub, hf, zero_smul, sub_zero, relation₁]
  · -- Case: `∀ i, f i ≠ 0`
    have _ : ∀ i ∈ t, 0 < f i := by
      intro i hi
      push_neg at hf
      exact zero_lt_iff.mpr (hf i hi)
    -- `relation₂: ∑ i : t, g i • ↑i = 0`
    -- `hnzero: g c ≠ 0`
    replace ⟨g, relation₂, c, hnzero⟩ := Fintype.not_linearIndependent_iff.1 h
    -- extend `g` to all of `E`
    let g' := Function.extend Subtype.val g 0
    -- For any `λ`, `∑ i in t, (f i + λ * g i) • i = x`.
    -- We choose a `λ` that make one of the coefficient `f i + λ * g i` while leaving all the other
    -- coefficients non-negative. The choice of `λ` depends on the signs of the coeffs `g i`.
    obtain (hneg | hpos) := Ne.lt_or_lt hnzero
    · -- Case: there is a negative coefficient `g c` in `relation₂`.
      -- Look at all the negative coefficients in `relation₂`.
      let s := @Finset.filter _ (fun z => g' z < 0) (fun _ => LinearOrder.decidableLT _ _) t
      -- Choose `λ = - max (f/g)` where the max is taken over all negative coefficients.
      obtain ⟨d, hd₁, hd₂⟩ := s.exists_max_image (fun z => f z / g' z) <| ⟨c, by {
        simpa only [filter_congr_decidable, Subtype.exists, exists_prop, exists_eq_right, not_lt,
          mem_filter, coe_mem, exists_apply_eq_apply, not_true_eq_false, true_and,
          Function.Injective.extend_apply Subtype.val_injective] }⟩
      rw [mem_filter] at hd₁
      use d, hd₁.1
      · -- Define new coefficients `k = f + λ g`
        let k : E → 𝕜≥0 := fun z => ⟨f z - f d / g' d * g' z, by {
        -- First we show that all `k i ≥ 0`
        rw [sub_nonneg]
        by_cases hzt : z ∈ t
        · by_cases hzs : z ∈ s
          · specialize hd₂ z hzs
            rw [mem_filter] at hzs
            rwa [← div_le_iff_of_neg hzs.2]
          · rw [mem_filter] at hzs
            push_neg at hzs
            exact le_trans (mul_nonpos_of_nonpos_of_nonneg
              (div_nonpos_of_nonneg_of_nonpos (zero_le <| f d)
                <| le_of_lt hd₁.2) (hzs hzt)) <| zero_le (f z)
        · have : g' z = 0 := by aesop
          rw [this, mul_zero]
          exact zero_le (f z) }⟩
        use k
        rw [sum_erase]
        · -- Proof of `∑ x in t, k x • x = x`
          simp only [Subtype.exists, exists_prop, exists_eq_right, Nonneg.mk_smul, sub_smul,
            Nonneg.coe_smul, Subtype.exists, exists_prop, exists_eq_right, sum_sub_distrib,
            relation₁, Subtype.exists, exists_prop, exists_eq_right, sub_eq_self, mul_smul,
            ← Finset.smul_sum]
          convert smul_zero (f d / g' d)
          rw [← relation₂]
          conv_lhs => rw [← Finset.sum_coe_sort]
          apply Finset.sum_congr rfl ?_
          rintro _ -
          rw [Function.Injective.extend_apply]
          exact Subtype.val_injective
        · -- At least one coefficient is 0.
          have : k d = 0 := by
            rw [Nonneg.mk_eq_zero, div_mul_cancel, sub_self]
            exact ne_of_lt hd₁.2
          rw [this, zero_smul]
    · -- Case: there is a positive coefficient `g c` in `relation₂`.
      -- Look at all the positive coefficients in `relation₂`.
      let s := @Finset.filter _ (fun z => 0 < g' z) (fun _ => LinearOrder.decidableLT _ _) t
      -- Choose `λ = - min (f/g)` where the min is taken over all positive coefficients.
      obtain ⟨d, hd₁, hd₂⟩ := s.exists_min_image (fun z => f z / g' z) <| ⟨c, by {
        simpa only [filter_congr_decidable, Subtype.exists, exists_prop, exists_eq_right, not_lt,
          mem_filter, coe_mem, exists_apply_eq_apply, not_true_eq_false, true_and,
          Function.Injective.extend_apply Subtype.val_injective] }⟩
      rw [mem_filter] at hd₁
      use d, hd₁.1
      · -- Define new coefficients `k = f + λ g`
        let k : E → 𝕜≥0 := fun z => ⟨f z - f d / g' d * g' z, by {
        -- First we show that all `k i ≥ 0`
        rw [sub_nonneg]
        by_cases hzt : z ∈ t
        · by_cases hzs : z ∈ s
          · specialize hd₂ z hzs
            rw [mem_filter] at hzs
            rwa [← le_div_iff hzs.2]
          · rw [mem_filter] at hzs
            push_neg at hzs
            exact le_trans (mul_nonpos_of_nonneg_of_nonpos
              (div_nonneg (zero_le (f d)) (le_of_lt hd₁.2)) (hzs hzt)) <| zero_le (f z)
        · have : g' z = 0 := by aesop
          rw [this, mul_zero]
          exact zero_le (f z) }⟩
        use k
        rw [sum_erase]
        · -- Proof of `∑ x in t, k x • x = x`
          simp only [Subtype.exists, exists_prop, exists_eq_right, Nonneg.mk_smul, sub_smul,
            Nonneg.coe_smul, Subtype.exists, exists_prop, exists_eq_right, sum_sub_distrib,
            relation₁, Subtype.exists, exists_prop, exists_eq_right, sub_eq_self, mul_smul,
            ← Finset.smul_sum]
          convert smul_zero (f d / g' d)
          rw [← relation₂]
          conv_lhs => rw [← Finset.sum_coe_sort]
          apply Finset.sum_congr rfl ?_
          rintro _ -
          rw [Function.Injective.extend_apply]
          exact Subtype.val_injective
        · -- At least one coefficient is 0.
          have : k d = 0 := by
            rw [Nonneg.mk_eq_zero, div_mul_cancel, sub_self]
            exact (ne_of_lt hd₁.2).symm
          rw [this, zero_smul]

variable {s : Set E} {x : E} (hx : x ∈ toPointedCone 𝕜 s)

/-- Given a point `x` in the convex cone of a set `s`, this is a finite subset of `s` of minimum
cardinality, whose convex cone contains `x`. -/
noncomputable def minCardFinsetOfMemtoPointedCone (hx : x ∈ s.toPointedCone 𝕜) : Finset E :=
  Function.argminOn Finset.card Nat.lt_wfRel.2 { t | ↑t ⊆ s ∧ x ∈ (t : Set E).toPointedCone 𝕜 }
    <| by exact Submodule.mem_span_finite_of_mem_span hx

theorem minCardFinsetOftoPointedCone_subseteq : ↑(minCardFinsetOfMemtoPointedCone hx) ⊆ s :=
  (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ (t : Set E).toPointedCone 𝕜 } _).1

theorem mem_minCardFinsetOfMemtoPointedCone :
    x ∈ (minCardFinsetOfMemtoPointedCone hx : Set E).toPointedCone 𝕜  := by
  have hs : Set.Nonempty {(t : Finset E) | (t : Set E) ⊆ s ∧ x ∈ toPointedCone 𝕜 ↑t} := by
    exact Submodule.mem_span_finite_of_mem_span hx
  have h := (Function.argminOn_mem Finset.card Nat.lt_wfRel.2
    { t : Finset E | ↑t ⊆ s ∧ x ∈ (t : Set E).toPointedCone 𝕜 } hs).2
  -- deterministic timeout if we use `exact` directly instead of the intermediate `have`
  exact h

theorem minCardFinsetOfMemtoPointedCone_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ (t : Set E).toPointedCone 𝕜) : (minCardFinsetOfMemtoPointedCone hx).card ≤ t.card :=
  Function.argminOn_le _ _ _ (by exact ⟨ht₁, ht₂⟩)

theorem linearIndependent_minCardFinsetOfMemtoPointedCone :
    LinearIndependent 𝕜 ((↑) : minCardFinsetOfMemtoPointedCone hx → E) := by
  by_cases h : minCardFinsetOfMemtoPointedCone hx = ∅
  · rw [h]
    exact linearIndependent_empty_type
  · have : 0 < (minCardFinsetOfMemtoPointedCone hx).card := by
      rw [card_pos]
      exact nonempty_of_ne_empty h
    set k := (minCardFinsetOfMemtoPointedCone hx).card - 1 with hk
    have hk : (minCardFinsetOfMemtoPointedCone hx).card = k + 1 := by
      rwa [hk, ← Nat.succ_eq_add_one, ← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos]
    classical
    by_contra h
    obtain ⟨p, hp⟩ := mem_toPointedCone_erase h (mem_minCardFinsetOfMemtoPointedCone hx)
    have contra := minCardFinsetOfMemtoPointedCone_card_le_card hx (Set.Subset.trans
      (Finset.erase_subset (p : E) (minCardFinsetOfMemtoPointedCone hx))
      (minCardFinsetOftoPointedCone_subseteq hx)) hp
    rw [← not_lt] at contra
    apply contra
    erw [card_erase_of_mem p.2, hk]
    exact lt_add_one _

end Caratheodory

variable {s : Set E}

/-- **Carathéodory's convexity theorem for convex cones** -/

theorem toPointedCone_eq_union : (s.toPointedCone 𝕜 : Set E) =
    ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : LinearIndependent 𝕜 ((↑) : t → E)),
      (SetLike.coe <| toPointedCone 𝕜 t) := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemtoPointedCone hx,
      Caratheodory.minCardFinsetOftoPointedCone_subseteq hx,
      Caratheodory.linearIndependent_minCardFinsetOfMemtoPointedCone hx,
      Caratheodory.mem_minCardFinsetOfMemtoPointedCone hx⟩
  · iterate 3 convert Set.iUnion_subset _; intro
    exact Submodule.span_mono ‹_›

/-- A more explicit version of `toPointedCone_eq_union`. -/
theorem mem_toPointedCone_iff_eq_pos_convex_span {x : E} : (x ∈ s.toPointedCone 𝕜) ↔
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜) (_ : Set.range z ⊆ s) (_ : LinearIndependent 𝕜 z)
        (_ : ∀ i, 0 < w i), ∑ i, w i • z i = x := by
  constructor
  · rintro hx
    rw [← SetLike.mem_coe, toPointedCone_eq_union] at hx
    simp only [exists_prop, Set.mem_iUnion] at hx
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
    simp_rw [toPointedCone, SetLike.mem_coe, mem_span_finset] at ht₃
    replace ⟨f, hf⟩ := ht₃
    simp only [exists_prop, exists_and_left]
    let t' := t.filter fun i => f i ≠ 0
    refine' ⟨t', t'.fintypeCoeSort, Subtype.val, ⟨_, _, (fun x => f x), _, _⟩⟩
    · rw [Subtype.range_coe_subtype]
      exact Subset.trans (Finset.filter_subset _ t) ht₁
    · exact @LinearIndependent.mono 𝕜 E _ _ _ t' t (t.filter_subset _) ht₂
    · rintro ⟨i, hi⟩
      rw [mem_filter] at hi
      refine' lt_of_le_of_ne _ _
      · exact zero_le (f i)
      · symm
        convert hi.2
        exact eq_iff_eq_of_cmp_eq_cmp rfl
    · have := @Finset.sum_subset E _ t' t (fun i => (f i) • i) _ (by aesop) (by aesop)
      conv_rhs => rw [← hf, ← this, ← Finset.sum_coe_sort]
  · rintro ⟨ι, _, f, c, _, -, hc, sum⟩
    rw [mem_span_set']
    set eq := (@Fintype.equivFin ι).symm with heq
    lift f to (ι → s)
    · aesop
    use (Fintype.card ι), fun x => ⟨(c ∘ eq) x, le_of_lt <| hc _⟩, f ∘ eq.1
    convert sum
    have := @Equiv.sum_comp (Fin (Fintype.card ι)) ι E _ _ _ (@Fintype.equivFin ι _).symm
      (fun x => c x • f x)
    rwa [← heq] at this
