/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Set.Lattice

/-!
# Unions and intersections of bounds

Some results about upper and lower bounds over collections of sets.

## Implementation notes

In a separate file as we need to import `Mathlib.Data.Set.Lattice` for `subset_iUnion_of_subset`.

-/

variable {α : Type*} [Preorder α]

open Set

theorem upperBounds_lowerBounds_gc : GaloisConnection
    (OrderDual.toDual ∘ upperBounds : Set α → (Set α)ᵒᵈ)
    (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ → Set α) := by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T ↦ forall₂_swap

theorem upperBounds_iUnion {ι : Sort*} {s : ι → Set α} :
    upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i)  :=
  upperBounds_lowerBounds_gc.l_iSup

theorem lowerBounds_iUnion {ι : Sort*} {s : ι → Set α} :
    lowerBounds (⋃ i, s i) = ⋂ i, lowerBounds (s i) :=
  upperBounds_lowerBounds_gc.u_iInf

theorem IsLUB.iUnion {ι : Sort*} {u : ι → α}  {s : ι → Set α} (hs : ∀ (i : ι), IsLUB (s i) (u i))
    (c : α) (hc : IsLUB (Set.range u ) c) : IsLUB (⋃ i, s i) c := by
  constructor
  · intro e he
    obtain ⟨i,hi⟩ := mem_iUnion.mp he
    obtain ⟨hc₁,hc₂⟩ := hc
    simp only [upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      mem_setOf_eq] at hc₁
    obtain ⟨hs₁,_⟩ := hs i
    exact Preorder.le_trans e (u i) c (hs₁ hi) (hc₁ i)
  · intro e he
    rw [upperBounds_iUnion] at he
    apply hc.2
    simp only [upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_setOf_eq]
    exact fun i => (hs i).2 (he _ (mem_range_self i))

theorem IsGLB.iUnion {ι : Sort*} {u : ι → α}  {s : ι → Set α} (hs : ∀ (i : ι), IsGLB (s i) (u i))
    (c : α) (hc : IsGLB (Set.range u ) c) : IsGLB (⋃ i, s i) c := by
  constructor
  · intro e he
    obtain ⟨i,hi⟩ := mem_iUnion.mp he
    obtain ⟨hc₁,hc₂⟩ := hc
    simp only [lowerBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      mem_setOf_eq] at hc₁
    obtain ⟨hs₁,_⟩ := hs i
    exact Preorder.le_trans c (u i) e (hc₁ i) (hs₁ hi)
  · intro e he
    rw [lowerBounds_iUnion] at he
    apply hc.2
    simp only [lowerBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_setOf_eq]
    exact fun i => (hs i).2 (he _ (mem_range_self i))
