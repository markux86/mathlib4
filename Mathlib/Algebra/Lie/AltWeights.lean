/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Finiteness.Nilpotent
import Batteries.Tactic.ShowUnused

/- We define the Submodules generated by repeatedly applying a linear map `f: V →ₗ[F] V`
to a vector `v`-/

namespace LinearMap.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
variable (x : M) (f : Module.End R M)

/-- The submodule generated by `v`, `f v`, `f f v`, ... , `f^[n-1] v`.-/
abbrev iteratedRange (n : ℕ) : Submodule R M :=
  Submodule.span R {(f^a) x | a < n}

lemma iteratedRange_mono {a b : ℕ} (h : a ≤ b) : iteratedRange x f a ≤ iteratedRange x f b :=
  Submodule.span_mono (fun _ ⟨c, hc, hw⟩ ↦ ⟨c, lt_of_lt_of_le hc h, hw⟩)

lemma map_iteratedRange_le (n : ℕ) :
    Submodule.map f (iteratedRange x f n) ≤ iteratedRange x f (n + 1) := by
  rw [Submodule.map_span]
  apply Submodule.span_mono
  suffices ∀ a < n, ∃ b < n + 1, (f ^ b) x = (f ^ (a + 1)) x by simpa [pow_succ']
  aesop

/-- The union of `iteratedRange` for all `n : ℕ`.-/
abbrev iSup_iteratedRange : Submodule R M := ⨆ k : ℕ, iteratedRange x f k

lemma map_iteratedRange_iSup_le_iSup :
    Submodule.map f (iSup_iteratedRange x f) ≤ iSup_iteratedRange x f := by
  rw [Submodule.map_iSup, iSup_le_iff]
  exact fun i ↦ (map_iteratedRange_le x f i).trans (le_iSup _ _)

end LinearMap.End

variable {R L A V : Type*} [CommRing R]
variable [LieRing L] [LieAlgebra R L]
variable [LieRing A] [LieAlgebra R A]
variable [LieRingModule L A]
variable [LieRingModule A L]
variable [AddCommGroup V] [Module R V]
variable [LieRingModule L V] [LieModule R L V]
variable [LieRingModule A V] [LieModule R A V]
variable [LieTower L A V] [LieTower A L V]

local notation "π" => LieModule.toEnd R _ V

variable (χ : A → R)

abbrev T (w : A) : Module.End R V := (π w) - χ w • 1

variable (z : L) (w : A) {v : V} (hv : ∀ w : A, ⁅w, v⁆ = (χ w) • v)

open LinearMap.End

include hv in
lemma T_apply_succ (n : ℕ) :
    Submodule.map (T χ w) (iteratedRange v (π z) (n + 1)) ≤ iteratedRange v (π z) n := by
  rw [Submodule.map_span, Submodule.span_le, Set.image_subset_iff]
  simp only [Set.subset_def, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  induction n generalizing w
  · simp only [zero_add, Nat.lt_one_iff, LinearMap.sub_apply, LieModule.toEnd_apply_apply,
      LinearMap.smul_apply, LinearMap.one_apply, forall_eq, pow_zero, hv w, sub_self, zero_mem]
  · next n hn =>
    intro m hm
    obtain (hm | rfl) : m < n + 1 ∨ m = n + 1 := by omega
    · exact iteratedRange_mono v _ (Nat.le_succ n) (hn w m hm)
    have H : ∀ w, ⁅w, (π z ^ n) v⁆ = (T χ w) ((π z ^ n) v) + χ w • ((π z ^ n) v) := by simp
    rw [T, LinearMap.sub_apply, pow_succ', LinearMap.mul_apply, LieModule.toEnd_apply_apply,
      LieModule.toEnd_apply_apply, LinearMap.smul_apply, LinearMap.one_apply, leibniz_lie,
      lie_swap_lie w z, H, H, lie_add, lie_smul, add_sub_assoc, add_sub_assoc, sub_self, add_zero]
    refine add_mem (neg_mem <| add_mem ?_ ?_) ?_
    · exact iteratedRange_mono v _ n.le_succ (hn _ n n.lt_succ_self)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, n.lt_succ_self, rfl⟩)
    · exact map_iteratedRange_le _ _ _ <| Submodule.mem_map_of_mem <| hn w n n.lt_succ_self

include hv in
lemma T_map_iSup_iteratedRange' :
    Submodule.map (T χ w) (iSup_iteratedRange v (π z)) ≤ iSup_iteratedRange v (π z) := by
  rw [Submodule.map_iSup, iSup_le_iff]
  rintro (_|i)
  · simp [Submodule.map_span]
  · exact (T_apply_succ χ z w hv i).trans (le_iSup _ _)

include hv in
lemma T_map_iSup_iteratedRange (x : V)
    (hx : x ∈ iSup_iteratedRange v (π z)) : (T χ w) x ∈ iSup_iteratedRange v (π z) :=
  T_map_iSup_iteratedRange' χ z w hv <| Submodule.mem_map_of_mem hx

def iSupIR : LieSubmodule R A V where
  toSubmodule := iSup_iteratedRange v (π z)
  lie_mem {w} x hx := by
    have hx' : ⁅w, x⁆ = (T χ w) x + χ w • x := by simp
    simpa only [hx'] using add_mem (T_map_iSup_iteratedRange χ z w hv x hx)
        (Submodule.smul_mem (iSup_iteratedRange v (π z)) _ hx)

include hv in
lemma T_map_iteratedRange_nilpotent (N : ℕ) :
    ∀ x ∈ (iteratedRange v (π z)) N, (T χ w ^ N) x = 0 := by
  induction N with
  | zero => simp [iteratedRange]
  | succ N ih =>
    intro x hx
    rw [pow_succ, LinearMap.mul_apply, ih]
    exact T_apply_succ χ z w hv N <| Submodule.mem_map_of_mem hx

theorem trace_πza_zero (a : A) :
    LinearMap.trace R (iSupIR χ z hv) (LieModule.toEnd R A _ ⁅z, a⁆) = 0 := by
  set U := iSupIR χ z hv
  have hzU : ∀ x ∈ U, (π z) x ∈ U :=
    fun _ hx ↦ (map_iteratedRange_iSup_le_iSup v (π z)) (Submodule.mem_map_of_mem hx)
  have hres : LieModule.toEnd R A U ⁅z, a⁆ = ⁅(π z).restrict hzU, LieModule.toEnd R A U a⁆ := by
    ext ⟨x, hx⟩
    simp only [LieModule.toEnd_apply_apply, LieSubmodule.coe_bracket, LieHom.lie_apply,
      Module.End.lie_apply, AddSubgroupClass.coe_sub]
    -- why do we need this `erw` now?
    erw [LinearMap.restrict_coe_apply, LinearMap.restrict_coe_apply]
    simp only [LieSubmodule.coe_bracket, LieModule.toEnd_apply_apply, leibniz_lie z a,
      add_sub_cancel_right]
  rw [hres, LieRing.of_associative_ring_bracket, map_sub, LinearMap.trace_mul_comm, sub_self]

variable [IsNoetherian R V]

theorem T_res_nilpotent :
    IsNilpotent ((T χ w).restrict (T_map_iSup_iteratedRange χ z w hv)) := by
  suffices iSup_iteratedRange v (π z) ≤ Module.End.maxGenEigenspace (T χ w) 0 by
    rw [Module.Finite.Module.End.isNilpotent_iff_of_finite]
    intro x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (T χ w ^ n) x.1 = 0 := by
      simpa [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero] using this x.2
    use n
    rw [LinearMap.pow_restrict, Subtype.ext_iff, LinearMap.restrict_apply, Subtype.coe_mk, hn,
      ZeroMemClass.coe_zero]
  apply iSup_le
  intro i x hx
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
  use i
  exact T_map_iteratedRange_nilpotent χ z w hv i x hx

theorem T_nilpotent : IsNilpotent ((T (V := iSupIR χ z hv) χ w)) := by
  suffices iSup_iteratedRange v (π z) ≤ Module.End.maxGenEigenspace (T χ w) 0 by
    rw [Module.Finite.Module.End.isNilpotent_iff_of_finite]
    intro x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (T χ w ^ n) x.1 = 0 := by
      simpa [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero] using this x.2
    use n
    ext
    simp only [ZeroMemClass.coe_zero, ← hn]; clear hn
    induction n <;> simp_all [pow_succ']
  apply iSup_le
  intro i x hx
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
  use i
  exact T_map_iteratedRange_nilpotent χ z w hv i x hx

variable [IsPrincipalIdealRing R]
variable [IsDomain R]
variable [Module.Free R V]

lemma trace_T_iSupIR_eq_zero : LinearMap.trace R (iSupIR χ z hv) (T χ w) = 0 :=
  LinearMap.isNilpotent_trace_of_isNilpotent (T_nilpotent χ z w hv) |>.eq_zero

open Module (finrank)
open LieModule

lemma trace_πza (a : A) :
    (toEnd R A _ ⁅z, a⁆).trace R (iSupIR χ z hv) = χ ⁅z, a⁆ • (finrank R (iSupIR χ z hv)) := by
  simpa [T, sub_eq_zero] using trace_T_iSupIR_eq_zero χ z ⁅z, a⁆ hv

variable [CharZero R]

lemma lie_stable (x : L) (v : V) (hv : v ∈ weightSpace V χ) : ⁅x, v⁆ ∈ weightSpace V χ := by
  rw [mem_weightSpace] at hv ⊢
  intro a
  rcases eq_or_ne v 0 with (rfl | hv')
  · simp only [lie_zero, smul_zero]
  suffices χ ⁅x, a⁆ = 0 by
    rw [leibniz_lie, hv a, lie_smul, lie_swap_lie, hv, this, zero_smul, neg_zero, zero_add]
  suffices finrank R ↥(iSupIR χ x hv) ≠ 0 by
    have := trace_πza χ x hv a
    simp_all [trace_πza_zero χ x hv a]
  suffices Nontrivial (iSupIR χ x hv) from Module.finrank_pos.ne'
  have hvU : v ∈ iSupIR χ x hv := by
    apply Submodule.mem_iSup_of_mem 1
    apply Submodule.subset_span
    use 0, zero_lt_one
    rw [pow_zero, LinearMap.one_apply]
  exact nontrivial_of_ne ⟨v, hvU⟩ 0 <| by simp [hv']

