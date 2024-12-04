/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.Algebra.Field
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Liouville's theorem

A proof of Liouville's theorem. Follows
[Rosenlicht, M. Integration in finite terms][Rosenlicht_1972].

## Liouville field extension

This file defines Liouville field extensions, which are differential field extensions which satisfy
a slight generalization of Liouville's theorem. Note that this definition doesn't appear in the
literature, and we introduce it as part of the formalization of Liouville's theorem.
-/

open Differential algebraMap IntermediateField Finset Polynomial

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K] [DifferentialAlgebra F K]

/--
We say that a differential field extension `K / F` is Liouville if, whenever an element a ∈ F can be
written as `a = v + ∑ cᵢ * logDeriv uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant, it can also be
written in that way with `v, cᵢ, uᵢ ∈ F`.
-/
class IsLiouville : Prop where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    ∃ (ι' : Type) (_ : Fintype ι') (c' : ι' → F) (_ : ∀ x, (c' x)′ = 0)
      (u' : ι' → F) (v' : F), a = ∑ x, c' x * logDeriv (u' x) + v'′

instance IsLiouville.rfl : IsLiouville F F where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → F) (v : F) (h : a = ∑ x, c x * logDeriv (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩

lemma IsLiouville.trans {A : Type*} [Field A] [Algebra K A] [Algebra F A]
    [Differential A] [IsScalarTower F K A] [Differential.ContainConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → A) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    obtain ⟨ι'', _, c'', hc', u'', v', h'⟩ := inst2.is_liouville (a : K) ι
        ((↑) ∘ c)
        (fun _ ↦ by simp only [Function.comp_apply, ← coe_deriv, lift_map_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι'') := mem_range_of_deriv_eq_zero F (hc' x)
    choose c' hc using hc
    apply inst1.is_liouville a ι'' c' _ u'' v'
    · rw [h']
      simp [hc]
    · intro
      apply_fun ((↑) : F → K)
      · simp only [Function.comp_apply, coe_deriv, hc, algebraMap.coe_zero]
        apply hc'
      · apply NoZeroSMulDivisors.algebraMap_injective

section Algebraic
/-
The case of Liouville's theorem for algebraic extensions.
-/

variable {F K} [CharZero F]

instance (B : IntermediateField F K)
    [FiniteDimensional F B] [inst : IsLiouville F K] :
    IsLiouville F B where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → B) (v : B) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.is_liouville a ι c hc (B.val ∘ u) (B.val v)
    dsimp only [coe_val, Function.comp_apply]
    conv =>
      rhs
      congr
      · rhs
        intro x
        rhs
        apply logDeriv_algebraMap (u x)
      · apply (deriv_algebraMap v)
    simp_rw [IsScalarTower.algebraMap_apply F B K]
    norm_cast


lemma IsLiouville.equiv {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
    [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K']
    [inst : IsLiouville F K] (e : K ≃ₐ[F] K') : IsLiouville F K' where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K') (v : K') (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.is_liouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

private local instance isLiouville_of_finiteDimensional_galois [FiniteDimensional F K]
    [IsGalois F K] : IsLiouville F K where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    haveI : CharZero K := charZero_of_injective_algebraMap
      (NoZeroSMulDivisors.algebraMap_injective F K)
    let c' (i : ι) := (c i) / (Fintype.card (K ≃ₐ[F] K))
    let u'' (i : ι) := ∏ x : (K ≃ₐ[F] K), x (u i)
    have : ∀ i, u'' i ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro i ⟨e, _⟩
      change e (u'' i) = u'' i
      simp only [u'', map_prod]
      apply Fintype.prod_equiv (Equiv.mulLeft e)
      simp
    have ffb : fixedField ⊤ = ⊥ := (IsGalois.tfae.out 0 1).mp (inferInstanceAs (IsGalois F K))
    simp_rw [ffb, IntermediateField.mem_bot, Set.mem_range] at this
    choose u' hu' using this
    let v'' := (∑ x : (K ≃ₐ[F] K), x v) / (Fintype.card ((K ≃ₐ[F] K)))
    have : v'' ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro ⟨e, _⟩
      change e v'' = v''
      simp only [v'', map_div₀, map_sum, map_natCast]
      congr 1
      apply Fintype.sum_equiv (Equiv.mulLeft e)
      simp
    rw [ffb, IntermediateField.mem_bot] at this
    obtain ⟨v', hv'⟩ := this
    exists ι, inferInstance, c', ?_, u', v'
    · intro x
      simp [c', Derivation.leibniz_div, hc]
    · apply_fun (algebraMap F K)
      case inj =>
        exact NoZeroSMulDivisors.algebraMap_injective F K
      simp only [map_add, map_sum, map_mul, ← logDeriv_algebraMap, hu', ← deriv_algebraMap, hv']
      unfold u'' v'' c'
      clear c' u'' u' hu' v'' v' hv'
      push_cast
      rw [Derivation.leibniz_div_const, smul_eq_mul, inv_mul_eq_div]
      case h => simp
      simp only [map_sum, div_mul_eq_mul_div]
      rw [← sum_div, ← add_div]
      field_simp
      -- Here we rewrite logDeriv (∏ x : K ≃ₐ[F] K, x (u i)) to ∑ x : K ≃ₐ[F] K, logDeriv (x (u i))
      conv =>
        enter [2, 1, 2, i, 2]
        tactic =>
          change _ = ∑ x : K ≃ₐ[F] K, logDeriv (x (u i))
          by_cases h : u i = 0
          · rw [logDeriv_prod_of_eq_zero]
            simp [h]
          · simp [logDeriv_prod, h]
      simp_rw [mul_sum]
      rw [sum_comm, ← sum_add_distrib]
      trans ∑ _ : (K ≃ₐ[F] K), a
      · simp [mul_comm]
      · rcongr e
        apply_fun e at h
        simp only [AlgEquiv.commutes, map_add, map_sum, map_mul] at h
        convert h using 2
        · rcongr x
          simp [logDeriv, algEquiv_deriv']
        · rw [algEquiv_deriv']

instance liouville_of_finiteDimensional [FiniteDimensional F K] :
    IsLiouville F K :=
  let map := (IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K))
  let K' := map.fieldRange
  have : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.restrict
    (F := K') (IntermediateField.le_normalClosure ..)
  have kequiv : K ≃ₐ[F] ↥B := (show K ≃ₐ[F] K' from AlgEquiv.ofInjectiveField map).trans
    (IntermediateField.restrict_algEquiv _)
  IsLiouville.equiv kequiv.symm

end Algebraic
