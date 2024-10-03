/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.MoveAdd

/-!
# Formal power series (in one variable)

This file defines (univariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

Formal power series in one variable are defined from multivariate
power series as `PowerSeries R := MvPowerSeries Unit R`.

The file sets up the (semi)ring structure on univariate power series.

We provide the natural inclusion from polynomials to formal power series.

Additional results can be found in:
* `Mathlib.RingTheory.PowerSeries.Trunc`, truncation of power series;
* `Mathlib.RingTheory.PowerSeries.Inverse`, about inverses of power series,
and the fact that power series over a local ring form a local ring;
* `Mathlib.RingTheory.PowerSeries.Order`, the order of a power series at 0,
and application to the fact that power series over an integral domain
form an integral domain.

## Implementation notes

Because of its definition,
  `PowerSeries R := MvPowerSeries Unit R`.
a lot of proofs and properties from the multivariate case
can be ported to the single variable case.
However, it means that formal power series are indexed by `Unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they were indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
def MvPowerSeries (σ : Type*) (R : Type*) :=
  (σ →₀ ℕ) → R
#align mv_power_series MvPowerSeries

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

instance [Inhabited R] : Inhabited (MvPowerSeries σ R) :=
  ⟨fun _ => default⟩

instance [Zero R] : Zero (MvPowerSeries σ R) :=
  Pi.instZero

instance [AddMonoid R] : AddMonoid (MvPowerSeries σ R) :=
  Pi.addMonoid

instance [AddGroup R] : AddGroup (MvPowerSeries σ R) :=
  Pi.addGroup

instance [AddCommMonoid R] : AddCommMonoid (MvPowerSeries σ R) :=
  Pi.addCommMonoid

instance [AddCommGroup R] : AddCommGroup (MvPowerSeries σ R) :=
  Pi.addCommGroup

instance [Nontrivial R] : Nontrivial (MvPowerSeries σ R) :=
  Function.nontrivial

instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R (MvPowerSeries σ A) :=
  Pi.module _ _ _

instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S (MvPowerSeries σ A) :=
  Pi.isScalarTower

section Semiring

variable (R) [Semiring R]

/-- The `n`th monomial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  letI := Classical.decEq σ
  LinearMap.stdBasis R (fun _ ↦ R) n
#align mv_power_series.monomial MvPowerSeries.monomial

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n
#align mv_power_series.coeff MvPowerSeries.coeff

variable {R}

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ} (h : ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ) : φ = ψ :=
  funext h
#align mv_power_series.ext MvPowerSeries.ext

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
theorem ext_iff {φ ψ : MvPowerSeries σ R} : φ = ψ ↔ ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ :=
  Function.funext_iff
#align mv_power_series.ext_iff MvPowerSeries.ext_iff

theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) :
    (monomial R n) = LinearMap.stdBasis R (fun _ ↦ R) n := by
  rw [monomial]
  -- unify the `Decidable` arguments
  convert rfl
#align mv_power_series.monomial_def MvPowerSeries.monomial_def

theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) :
    coeff R m (monomial R n a) = if m = n then a else 0 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [coeff, monomial_def, LinearMap.proj_apply (i := m)]
  dsimp only
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LinearMap.stdBasis_apply, Function.update_apply, Pi.zero_apply]
#align mv_power_series.coeff_monomial MvPowerSeries.coeff_monomial

@[simp]
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff R n (monomial R n a) = a := by
  classical
  rw [monomial_def]
  exact LinearMap.stdBasis_same R (fun _ ↦ R) n a
#align mv_power_series.coeff_monomial_same MvPowerSeries.coeff_monomial_same

theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff R m (monomial R n a) = 0 := by
  classical
  rw [monomial_def]
  exact LinearMap.stdBasis_ne R (fun _ ↦ R) _ _ h a
#align mv_power_series.coeff_monomial_ne MvPowerSeries.coeff_monomial_ne

theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff R m (monomial R n a) ≠ 0) :
    m = n :=
  by_contra fun h' => h <| coeff_monomial_ne h' a
#align mv_power_series.eq_of_coeff_monomial_ne_zero MvPowerSeries.eq_of_coeff_monomial_ne_zero

@[simp]
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n
#align mv_power_series.coeff_comp_monomial MvPowerSeries.coeff_comp_monomial

-- Porting note: simp can prove this.
-- @[simp]
theorem coeff_zero (n : σ →₀ ℕ) : coeff R n (0 : MvPowerSeries σ R) = 0 :=
  rfl
#align mv_power_series.coeff_zero MvPowerSeries.coeff_zero

variable (m n : σ →₀ ℕ) (φ ψ : MvPowerSeries σ R)

instance : One (MvPowerSeries σ R) :=
  ⟨monomial R (0 : σ →₀ ℕ) 1⟩

theorem coeff_one [DecidableEq σ] : coeff R n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _
#align mv_power_series.coeff_one MvPowerSeries.coeff_one

theorem coeff_zero_one : coeff R (0 : σ →₀ ℕ) 1 = 1 :=
  coeff_monomial_same 0 1
#align mv_power_series.coeff_zero_one MvPowerSeries.coeff_zero_one

theorem monomial_zero_one : monomial R (0 : σ →₀ ℕ) 1 = 1 :=
  rfl
#align mv_power_series.monomial_zero_one MvPowerSeries.monomial_zero_one

instance : AddMonoidWithOne (MvPowerSeries σ R) :=
  { show AddMonoid (MvPowerSeries σ R) by infer_instance with
    natCast := fun n => monomial R 0 n
    natCast_zero := by simp [Nat.cast]
    natCast_succ := by simp [Nat.cast, monomial_zero_one]
    one := 1 }

instance : Mul (MvPowerSeries σ R) :=
  letI := Classical.decEq σ
  ⟨fun φ ψ n => ∑ p in antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ⟩

theorem coeff_mul [DecidableEq σ] :
    coeff R n (φ * ψ) = ∑ p in antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]
#align mv_power_series.coeff_mul MvPowerSeries.coeff_mul

protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by classical simp [coeff_mul]
#align mv_power_series.zero_mul MvPowerSeries.zero_mul

protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by classical simp [coeff_mul]
#align mv_power_series.mul_zero MvPowerSeries.mul_zero

theorem coeff_monomial_mul (a : R) :
    coeff R m (monomial R n a * φ) = if n ≤ m then a * coeff R (m - n) φ else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial R n a) * coeff R p.2 φ ≠ 0 → p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.filter_fst_eq_antidiagonal _ n,
    Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
#align mv_power_series.coeff_monomial_mul MvPowerSeries.coeff_monomial_mul

theorem coeff_mul_monomial (a : R) :
    coeff R m (φ * monomial R n a) = if n ≤ m then coeff R (m - n) φ * a else 0 := by
  classical
  have :
    ∀ p ∈ antidiagonal m,
      coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff R p.2 (monomial R n a) ≠ 0 → p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, Finset.filter_snd_eq_antidiagonal _ n,
    Finset.sum_ite_index]
  simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]
#align mv_power_series.coeff_mul_monomial MvPowerSeries.coeff_mul_monomial

theorem coeff_add_monomial_mul (a : R) :
    coeff R (m + n) (monomial R m a * φ) = a * coeff R n φ := by
  rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
  exact le_add_right le_rfl
#align mv_power_series.coeff_add_monomial_mul MvPowerSeries.coeff_add_monomial_mul

theorem coeff_add_mul_monomial (a : R) :
    coeff R (m + n) (φ * monomial R n a) = coeff R m φ * a := by
  rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
  exact le_add_left le_rfl
#align mv_power_series.coeff_add_mul_monomial MvPowerSeries.coeff_add_mul_monomial

@[simp]
theorem commute_monomial {a : R} {n} :
    Commute φ (monomial R n a) ↔ ∀ m, Commute (coeff R m φ) a := by
  refine' ext_iff.trans ⟨fun h m => _, fun h m => _⟩
  · have := h (m + n)
    rwa [coeff_add_mul_monomial, add_comm, coeff_add_monomial_mul] at this
  · rw [coeff_mul_monomial, coeff_monomial_mul]
    split_ifs <;> [apply h; rfl]
#align mv_power_series.commute_monomial MvPowerSeries.commute_monomial

protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by simpa using coeff_add_monomial_mul 0 n φ 1
#align mv_power_series.one_mul MvPowerSeries.one_mul

protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by simpa using coeff_add_mul_monomial n 0 φ 1
#align mv_power_series.mul_one MvPowerSeries.mul_one

protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, mul_add, Finset.sum_add_distrib, LinearMap.map_add]
#align mv_power_series.mul_add MvPowerSeries.mul_add

protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by
    classical simp only [coeff_mul, add_mul, Finset.sum_add_distrib, LinearMap.map_add]
#align mv_power_series.add_mul MvPowerSeries.add_mul

protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc, mul_assoc])
#align mv_power_series.mul_assoc MvPowerSeries.mul_assoc

instance : Semiring (MvPowerSeries σ R) :=
  { inferInstanceAs (AddMonoidWithOne (MvPowerSeries σ R)),
    inferInstanceAs (Mul (MvPowerSeries σ R)),
    inferInstanceAs (AddCommMonoid (MvPowerSeries σ R)) with
    mul_one := MvPowerSeries.mul_one
    one_mul := MvPowerSeries.one_mul
    mul_assoc := MvPowerSeries.mul_assoc
    mul_zero := MvPowerSeries.mul_zero
    zero_mul := MvPowerSeries.zero_mul
    left_distrib := MvPowerSeries.mul_add
    right_distrib := MvPowerSeries.add_mul }

end Semiring

instance [CommSemiring R] : CommSemiring (MvPowerSeries σ R) :=
  { show Semiring (MvPowerSeries σ R) by infer_instance with
    mul_comm := fun φ ψ =>
      ext fun n => by
        classical
        simpa only [coeff_mul, mul_comm] using
          sum_antidiagonal_swap n fun a b => coeff R a φ * coeff R b ψ }

instance [Ring R] : Ring (MvPowerSeries σ R) :=
  { inferInstanceAs (Semiring (MvPowerSeries σ R)),
    inferInstanceAs (AddCommGroup (MvPowerSeries σ R)) with }

instance [CommRing R] : CommRing (MvPowerSeries σ R) :=
  { inferInstanceAs (CommSemiring (MvPowerSeries σ R)),
    inferInstanceAs (AddCommGroup (MvPowerSeries σ R)) with }

section Semiring

variable [Semiring R]

theorem monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) :
    monomial R m a * monomial R n b = monomial R (m + n) (a * b) := by
  classical
  ext k
  simp only [coeff_mul_monomial, coeff_monomial]
  split_ifs with h₁ h₂ h₃ h₃ h₂ <;> try rfl
  · rw [← h₂, tsub_add_cancel_of_le h₁] at h₃
    exact (h₃ rfl).elim
  · rw [h₃, add_tsub_cancel_right] at h₂
    exact (h₂ rfl).elim
  · exact zero_mul b
  · rw [h₂] at h₁
    exact (h₁ <| le_add_left le_rfl).elim
#align mv_power_series.monomial_mul_monomial MvPowerSeries.monomial_mul_monomial

variable (σ) (R)

/-- The constant multivariate formal power series.-/
def C : R →+* MvPowerSeries σ R :=
  { monomial R (0 : σ →₀ ℕ) with
    map_one' := rfl
    map_mul' := fun a b => (monomial_mul_monomial 0 0 a b).symm
    map_zero' := (monomial R (0 : _)).map_zero }
set_option linter.uppercaseLean3 false in
#align mv_power_series.C MvPowerSeries.C

variable {σ} {R}

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R (0 : σ →₀ ℕ)) = C σ R :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.monomial_zero_eq_C MvPowerSeries.monomial_zero_eq_C

theorem monomial_zero_eq_C_apply (a : R) : monomial R (0 : σ →₀ ℕ) a = C σ R a :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.monomial_zero_eq_C_apply MvPowerSeries.monomial_zero_eq_C_apply

theorem coeff_C [DecidableEq σ] (n : σ →₀ ℕ) (a : R) :
    coeff R n (C σ R a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_C MvPowerSeries.coeff_C

theorem coeff_zero_C (a : R) : coeff R (0 : σ →₀ ℕ) (C σ R a) = a :=
  coeff_monomial_same 0 a
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_C MvPowerSeries.coeff_zero_C

/-- The variables of the multivariate formal power series ring.-/
def X (s : σ) : MvPowerSeries σ R :=
  monomial R (single s 1) 1
set_option linter.uppercaseLean3 false in
#align mv_power_series.X MvPowerSeries.X

theorem coeff_X [DecidableEq σ] (n : σ →₀ ℕ) (s : σ) :
    coeff R n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_X MvPowerSeries.coeff_X

theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
    coeff R (single t 1) (X s : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  simp only [coeff_X, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_index_single_X MvPowerSeries.coeff_index_single_X

@[simp]
theorem coeff_index_single_self_X (s : σ) : coeff R (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_index_single_self_X MvPowerSeries.coeff_index_single_self_X

theorem coeff_zero_X (s : σ) : coeff R (0 : σ →₀ ℕ) (X s : MvPowerSeries σ R) = 0 := by
  classical
  rw [coeff_X, if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_X MvPowerSeries.coeff_zero_X

theorem commute_X (φ : MvPowerSeries σ R) (s : σ) : Commute φ (X s) :=
  φ.commute_monomial.mpr fun _m => Commute.one_right _
set_option linter.uppercaseLean3 false in
#align mv_power_series.commute_X MvPowerSeries.commute_X

theorem X_def (s : σ) : X s = monomial R (single s 1) 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_def MvPowerSeries.X_def

theorem X_pow_eq (s : σ) (n : ℕ) : (X s : MvPowerSeries σ R) ^ n = monomial R (single s n) 1 := by
  induction' n with n ih
  · simp
  · rw [pow_succ', ih, Nat.succ_eq_add_one, Finsupp.single_add, X, monomial_mul_monomial, one_mul]
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_pow_eq MvPowerSeries.X_pow_eq

theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
    coeff R m ((X s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n, coeff_monomial]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_X_pow MvPowerSeries.coeff_X_pow

@[simp]
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff R n (φ * C σ R a) = coeff R n φ * a := by simpa using coeff_add_mul_monomial n 0 φ a
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_mul_C MvPowerSeries.coeff_mul_C

@[simp]
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) :
    coeff R n (C σ R a * φ) = a * coeff R n φ := by simpa using coeff_add_monomial_mul 0 n φ a
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_C_mul MvPowerSeries.coeff_C_mul

theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (φ * X s) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by simpa using h s
  simp only [X, coeff_mul_monomial, if_neg this]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_mul_X MvPowerSeries.coeff_zero_mul_X

theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (X s * φ) = 0 := by
  rw [← (φ.commute_X s).eq, coeff_zero_mul_X]
set_option linter.uppercaseLean3 false in
#align mv_power_series.coeff_zero_X_mul MvPowerSeries.coeff_zero_X_mul

variable (σ) (R)

/-- The constant coefficient of a formal power series.-/
def constantCoeff : MvPowerSeries σ R →+* R :=
  { coeff R (0 : σ →₀ ℕ) with
    toFun := coeff R (0 : σ →₀ ℕ)
    map_one' := coeff_zero_one
    map_mul' := fun φ ψ => by classical simp [coeff_mul, support_single_ne_zero]
    map_zero' := LinearMap.map_zero _ }
#align mv_power_series.constant_coeff MvPowerSeries.constantCoeff

variable {σ} {R}

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff R (0 : σ →₀ ℕ)) = constantCoeff σ R :=
  rfl
#align mv_power_series.coeff_zero_eq_constant_coeff MvPowerSeries.coeff_zero_eq_constantCoeff

theorem coeff_zero_eq_constantCoeff_apply (φ : MvPowerSeries σ R) :
    coeff R (0 : σ →₀ ℕ) φ = constantCoeff σ R φ :=
  rfl
#align mv_power_series.coeff_zero_eq_constant_coeff_apply MvPowerSeries.coeff_zero_eq_constantCoeff_apply

@[simp]
theorem constantCoeff_C (a : R) : constantCoeff σ R (C σ R a) = a :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.constant_coeff_C MvPowerSeries.constantCoeff_C

@[simp]
theorem constantCoeff_comp_C : (constantCoeff σ R).comp (C σ R) = RingHom.id R :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.constant_coeff_comp_C MvPowerSeries.constantCoeff_comp_C

-- Porting note: simp can prove this.
-- @[simp]
theorem constantCoeff_zero : constantCoeff σ R 0 = 0 :=
  rfl
#align mv_power_series.constant_coeff_zero MvPowerSeries.constantCoeff_zero

-- Porting note: simp can prove this.
-- @[simp]
theorem constantCoeff_one : constantCoeff σ R 1 = 1 :=
  rfl
#align mv_power_series.constant_coeff_one MvPowerSeries.constantCoeff_one

@[simp]
theorem constantCoeff_X (s : σ) : constantCoeff σ R (X s) = 0 :=
  coeff_zero_X s
set_option linter.uppercaseLean3 false in
#align mv_power_series.constant_coeff_X MvPowerSeries.constantCoeff_X

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
theorem isUnit_constantCoeff (φ : MvPowerSeries σ R) (h : IsUnit φ) :
    IsUnit (constantCoeff σ R φ) :=
  h.map _
#align mv_power_series.is_unit_constant_coeff MvPowerSeries.isUnit_constantCoeff

-- Porting note: simp can prove this.
-- @[simp]
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff _ n (a • f) = a * coeff _ n f :=
  rfl
#align mv_power_series.coeff_smul MvPowerSeries.coeff_smul

theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = C σ R a * f := by
  ext
  simp
set_option linter.uppercaseLean3 false in
#align mv_power_series.smul_eq_C_mul MvPowerSeries.smul_eq_C_mul

theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by
    classical
    intro h
    replace h := congr_arg (coeff R (single s 1)) h
    rw [coeff_X, if_pos rfl, coeff_X] at h
    split_ifs at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      cases' H with H H
      · exact H.1
      · exfalso
        exact one_ne_zero H.1
    · exfalso
      exact one_ne_zero h, congr_arg X⟩
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_inj MvPowerSeries.X_inj

end Semiring

section Map

variable {S T : Type*} [Semiring R] [Semiring S] [Semiring T]

variable (f : R →+* S) (g : S →+* T)

variable (σ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S where
  toFun φ n := f <| coeff R n φ
  map_zero' := ext fun _n => f.map_zero
  map_one' :=
    ext fun n =>
      show f ((coeff R n) 1) = (coeff S n) 1 by
        classical
        rw [coeff_one, coeff_one]
        split_ifs with h
        · simp only [RingHom.map_ite_one_zero, ite_true, map_one, h]
        · simp only [RingHom.map_ite_one_zero, ite_false, map_zero, h]
  map_add' φ ψ :=
    ext fun n => show f ((coeff R n) (φ + ψ)) = f ((coeff R n) φ) + f ((coeff R n) ψ) by simp
  map_mul' φ ψ :=
    ext fun n =>
      show f _ = _ by
        classical
        rw [coeff_mul, map_sum, coeff_mul]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ _; rw [f.map_mul]; rfl
#align mv_power_series.map MvPowerSeries.map

variable {σ}

@[simp]
theorem map_id : map σ (RingHom.id R) = RingHom.id _ :=
  rfl
#align mv_power_series.map_id MvPowerSeries.map_id

theorem map_comp : map σ (g.comp f) = (map σ g).comp (map σ f) :=
  rfl
#align mv_power_series.map_comp MvPowerSeries.map_comp

@[simp]
theorem coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) : coeff S n (map σ f φ) = f (coeff R n φ) :=
  rfl
#align mv_power_series.coeff_map MvPowerSeries.coeff_map

@[simp]
theorem constantCoeff_map (φ : MvPowerSeries σ R) :
    constantCoeff σ S (map σ f φ) = f (constantCoeff σ R φ) :=
  rfl
#align mv_power_series.constant_coeff_map MvPowerSeries.constantCoeff_map

@[simp]
theorem map_monomial (n : σ →₀ ℕ) (a : R) : map σ f (monomial R n a) = monomial S n (f a) := by
  classical
  ext m
  simp [coeff_monomial, apply_ite f]
#align mv_power_series.map_monomial MvPowerSeries.map_monomial

@[simp]
theorem map_C (a : R) : map σ f (C σ R a) = C σ S (f a) :=
  map_monomial _ _ _
set_option linter.uppercaseLean3 false in
#align mv_power_series.map_C MvPowerSeries.map_C

@[simp]
theorem map_X (s : σ) : map σ f (X s) = X s := by simp [MvPowerSeries.X]
set_option linter.uppercaseLean3 false in
#align mv_power_series.map_X MvPowerSeries.map_X

end Map

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

instance : Algebra R (MvPowerSeries σ A) :=
  {
    show Module R (MvPowerSeries σ A) by infer_instance with
    commutes' := fun a φ => by
      ext n
      simp [Algebra.commutes]
    smul_def' := fun a σ => by
      ext n
      simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def]
    toRingHom := (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) }

theorem c_eq_algebraMap : C σ R = algebraMap R (MvPowerSeries σ R) :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_power_series.C_eq_algebra_map MvPowerSeries.c_eq_algebraMap

theorem algebraMap_apply {r : R} :
    algebraMap R (MvPowerSeries σ A) r = C σ A (algebraMap R A r) := by
  change (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) r = _
  simp
#align mv_power_series.algebra_map_apply MvPowerSeries.algebraMap_apply

instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      classical
      rw [Ne.def, SetLike.ext_iff, not_forall]
      inhabit σ
      refine' ⟨X default, _⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      intro x
      rw [ext_iff, not_forall]
      refine' ⟨Finsupp.single default 1, _⟩
      simp [algebraMap_apply, coeff_C]⟩⟩

end Algebra

section Trunc

variable [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m in Finset.Iio n, MvPolynomial.monomial m (coeff R m φ)
#align mv_power_series.trunc_fun MvPowerSeries.truncFun

theorem coeff_truncFun [DecidableEq σ] (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical
  simp [truncFun, MvPolynomial.coeff_sum]
#align mv_power_series.coeff_trunc_fun MvPowerSeries.coeff_truncFun

variable (R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    classical
    ext
    simp [coeff_truncFun]
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun, MvPolynomial.coeff_add]
    split_ifs
    · rw [map_add]
    · rw [zero_add]

#align mv_power_series.trunc MvPowerSeries.trunc

variable {R}

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical simp [trunc, coeff_truncFun]
#align mv_power_series.coeff_trunc MvPowerSeries.coeff_trunc

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc, coeff_one]
    split_ifs with H H'
    · subst m
      simp
    · symm
      rw [MvPolynomial.coeff_one]
      exact if_neg (Ne.symm H')
    · symm
      rw [MvPolynomial.coeff_one]
      refine' if_neg _
      rintro rfl
      apply H
      exact Ne.bot_lt hnn
#align mv_power_series.trunc_one MvPowerSeries.trunc_one

@[simp]
theorem trunc_c (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first |rfl|try simp_all
    exfalso; apply H; subst m; exact Ne.bot_lt hnn
set_option linter.uppercaseLean3 false in
#align mv_power_series.trunc_C MvPowerSeries.trunc_c

end Trunc

section Semiring

variable [Semiring R]

theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff R m φ = 0 := by
  classical
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul, Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow, if_neg, zero_mul]
    contrapose! h
    dsimp at h
    subst i
    rw [mem_antidiagonal] at hij
    rw [← hij, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_right n _
  · intro h
    refine' ⟨fun m => coeff R (m + single s n) φ, _⟩
    ext m
    by_cases H : m - single s n + single s n = m
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mul]
        simpa using congr_arg (fun m : σ →₀ ℕ => coeff R m φ) H.symm
      · rintro ⟨i, j⟩ hij hne
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply hne
          rw [← hij, ← hi, Prod.mk.inj_iff]
          refine' ⟨rfl, _⟩
          ext t
          simp only [add_tsub_cancel_left, Finsupp.add_apply, Finsupp.tsub_apply]
        · exact zero_mul _
      · intro hni
        exfalso
        apply hni
        rwa [mem_antidiagonal, add_comm]
    · rw [h, coeff_mul, Finset.sum_eq_zero]
      · rintro ⟨i, j⟩ hij
        rw [mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply H
          rw [← hij, hi]
          ext
          rw [coe_add, coe_add, Pi.add_apply, Pi.add_apply, add_tsub_cancel_left, add_comm]
        · exact zero_mul _
      · contrapose! H
        ext t
        by_cases hst : s = t
        · subst t
          simpa using tsub_add_cancel_of_le H
        · simp [Finsupp.single_apply, hst]
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_pow_dvd_iff MvPowerSeries.X_pow_dvd_iff

theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (X s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff R m φ = 0 := by
  rw [← pow_one (X s : MvPowerSeries σ R), X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
  · exact h m (Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ hm)
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_dvd_iff MvPowerSeries.X_dvd_iff

end Semiring

section Ring

variable [Ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coefficients of the inverse.
-/
/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `invOfUnit`.-/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    letI := Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x in antidiagonal n, if _ : x.2 < n then coeff R x.1 φ * inv.aux a φ x.2 else 0
termination_by _ n => n
#align mv_power_series.inv.aux MvPowerSeries.inv.aux

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff R n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x in antidiagonal n, if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl
#align mv_power_series.coeff_inv_aux MvPowerSeries.coeff_inv_aux

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ
#align mv_power_series.inv_of_unit MvPowerSeries.invOfUnit

theorem coeff_invOfUnit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x in antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 := by
  convert coeff_inv_aux n (↑u⁻¹) φ
#align mv_power_series.coeff_inv_of_unit MvPowerSeries.coeff_invOfUnit

@[simp]
theorem constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) :
    constantCoeff σ R (invOfUnit φ u) = ↑u⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]
#align mv_power_series.constant_coeff_inv_of_unit MvPowerSeries.constantCoeff_invOfUnit

theorem mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff σ R φ = u) :
    φ * invOfUnit φ u = 1 :=
  ext fun n =>
    letI := Classical.decEq (σ →₀ ℕ)
    if H : n = 0 then by
      rw [H]
      simp [coeff_mul, support_single_ne_zero, h]
    else by
      classical
      have : ((0 : σ →₀ ℕ), n) ∈ antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one, if_neg H, coeff_mul, ← Finset.insert_erase this,
        Finset.sum_insert (Finset.not_mem_erase _ _), coeff_zero_eq_constantCoeff_apply, h,
        coeff_invOfUnit, if_neg H, neg_mul, mul_neg, Units.mul_inv_cancel_left, ←
        Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _),
        Finset.insert_erase this, if_neg (not_lt_of_ge <| le_rfl), zero_add, add_comm, ←
        sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase, mem_antidiagonal] at hij
      cases' hij with h₁ h₂
      subst n
      rw [if_pos]
      suffices (0 : _) + j < i + j by simpa
      apply add_lt_add_right
      constructor
      · intro s
        exact Nat.zero_le _
      · intro H
        apply h₁
        suffices i = 0 by simp [this]
        ext1 s
        exact Nat.eq_zero_of_le_zero (H s)
#align mv_power_series.mul_inv_of_unit MvPowerSeries.mul_invOfUnit

end Ring

section CommRing

variable [CommRing R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance [LocalRing R] : LocalRing (MvPowerSeries σ R) :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self <| by
    intro φ
    rcases LocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff σ R φ) with (⟨u, h⟩ | ⟨u, h⟩) <;>
        [left; right] <;>
      · refine' isUnit_of_mul_eq_one _ _ (mul_invOfUnit _ u _)
        simpa using h.symm

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRing

section LocalRing

variable {S : Type*} [CommRing R] [Semiring S] (f : R →+* S) [IsLocalRingHom f]

-- Thanks to the linter for informing us that this instance does
-- not actually need R and S to be local rings!
/-- The map `A[[X]] → B[[X]]` induced by a local ring hom `A → B` is local -/
instance map.isLocalRingHom : IsLocalRingHom (map σ f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg (constantCoeff σ S) h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff σ S ↑ψ) := isUnit_constantCoeff (↑ψ) ψ.isUnit
    rw [h] at this
    rcases this.of_map with ⟨c, hc⟩
    exact isUnit_of_mul_eq_one φ (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩
#align mv_power_series.map.is_local_ring_hom MvPowerSeries.map.isLocalRingHom

end LocalRing

section Field

variable {k : Type*} [Field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  inv.aux (constantCoeff σ k φ)⁻¹ φ
#align mv_power_series.inv MvPowerSeries.inv

instance : Inv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩

theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff σ k φ)⁻¹
      else
        -(constantCoeff σ k φ)⁻¹ *
          ∑ x in antidiagonal n, if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  coeff_inv_aux n _ φ
#align mv_power_series.coeff_inv MvPowerSeries.coeff_inv

@[simp]
theorem constantCoeff_inv (φ : MvPowerSeries σ k) :
    constantCoeff σ k φ⁻¹ = (constantCoeff σ k φ)⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_inv, if_pos rfl]
#align mv_power_series.constant_coeff_inv MvPowerSeries.constantCoeff_inv

theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff σ k φ = 0 :=
  ⟨fun h => by simpa using congr_arg (constantCoeff σ k) h, fun h =>
    ext fun n => by
      classical
      rw [coeff_inv]
      split_ifs <;>
        simp only [h, map_zero, zero_mul, inv_zero, neg_zero]⟩
#align mv_power_series.inv_eq_zero MvPowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_zero]
#align mv_power_series.zero_inv MvPowerSeries.zero_inv

-- Porting note: simp can prove this.
-- @[simp]
theorem invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl
#align mv_power_series.inv_of_unit_eq MvPowerSeries.invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff σ k φ = u) :
    invOfUnit φ u = φ⁻¹ := by
  rw [← invOfUnit_eq φ (h.symm ▸ u.ne_zero)]
  apply congrArg (invOfUnit φ)
  rw [Units.ext_iff]
  exact h.symm
#align mv_power_series.inv_of_unit_eq' MvPowerSeries.invOfUnit_eq'

@[simp]
protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    φ * φ⁻¹ = 1 := by rw [← invOfUnit_eq φ h, mul_invOfUnit φ (Units.mk0 _ h) rfl]
#align mv_power_series.mul_inv_cancel MvPowerSeries.mul_inv_cancel

@[simp]
protected theorem inv_mul_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) :
    φ⁻¹ * φ = 1 := by rw [mul_comm, φ.mul_inv_cancel h]
#align mv_power_series.inv_mul_cancel MvPowerSeries.inv_mul_cancel

protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k}
    (h : constantCoeff σ k φ₃ ≠ 0) : φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  ⟨fun k => by simp [k, mul_assoc, MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [← k, mul_assoc, MvPowerSeries.mul_inv_cancel _ h]⟩
#align mv_power_series.eq_mul_inv_iff_mul_eq MvPowerSeries.eq_mul_inv_iff_mul_eq

protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) :
    φ = ψ⁻¹ ↔ φ * ψ = 1 := by rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mul]
#align mv_power_series.eq_inv_iff_mul_eq_one MvPowerSeries.eq_inv_iff_mul_eq_one

protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) :
    ψ⁻¹ = φ ↔ φ * ψ = 1 := by rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]
#align mv_power_series.inv_eq_iff_mul_eq_one MvPowerSeries.inv_eq_iff_mul_eq_one

@[simp]
protected theorem mul_inv_rev (φ ψ : MvPowerSeries σ k) :
    (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ := by
  by_cases h : constantCoeff σ k (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [map_mul, mul_eq_zero] at h
    -- we don't have `NoZeroDivisors (MvPowerSeries σ k)` yet,
    cases' h with h h <;> simp [inv_eq_zero.mpr h]
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [not_or, map_mul, mul_eq_zero] at h
    rw [← mul_assoc, mul_assoc _⁻¹, MvPowerSeries.inv_mul_cancel _ h.left, mul_one,
      MvPowerSeries.inv_mul_cancel _ h.right]
#align mv_power_series.mul_inv_rev MvPowerSeries.mul_inv_rev

instance : InvOneClass (MvPowerSeries σ k) :=
  { inferInstanceAs (One (MvPowerSeries σ k)),
    inferInstanceAs (Inv (MvPowerSeries σ k)) with
    inv_one := by
      rw [MvPowerSeries.inv_eq_iff_mul_eq_one, mul_one]
      simp }

@[simp]
theorem C_inv (r : k) : (C σ k r)⁻¹ = C σ k r⁻¹ := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ← map_mul, inv_mul_cancel hr, map_one]
  simpa using hr
set_option linter.uppercaseLean3 false in
#align mv_power_series.C_inv MvPowerSeries.C_inv

@[simp]
theorem X_inv (s : σ) : (X s : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constantCoeff_X]
set_option linter.uppercaseLean3 false in
#align mv_power_series.X_inv MvPowerSeries.X_inv

@[simp]
theorem smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ := by
  simp [smul_eq_C_mul, mul_comm]
#align mv_power_series.smul_inv MvPowerSeries.smul_inv

end Field

end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : MvPolynomial σ R)

-- Porting note: added so we can add the `@[coe]` attribute
/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
@[coe]
def toMvPowerSeries : MvPolynomial σ R → MvPowerSeries σ R :=
  fun φ n => coeff n φ

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
instance coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨toMvPowerSeries⟩
#align mv_polynomial.coe_to_mv_power_series MvPolynomial.coeToMvPowerSeries

theorem coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ :=
  rfl
#align mv_polynomial.coe_def MvPolynomial.coe_def

@[simp, norm_cast]
theorem coeff_coe (n : σ →₀ ℕ) : MvPowerSeries.coeff R n ↑φ = coeff n φ :=
  rfl
#align mv_polynomial.coeff_coe MvPolynomial.coeff_coe

@[simp, norm_cast]
theorem coe_monomial (n : σ →₀ ℕ) (a : R) :
    (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial R n a :=
  MvPowerSeries.ext fun m => by
    classical
    rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;> first |rfl|subst m; contradiction
#align mv_polynomial.coe_monomial MvPolynomial.coe_monomial

@[simp, norm_cast]
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl
#align mv_polynomial.coe_zero MvPolynomial.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
    coe_monomial _ _
#align mv_polynomial.coe_one MvPolynomial.coe_one

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ :=
  rfl
#align mv_polynomial.coe_add MvPolynomial.coe_add

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ :=
  MvPowerSeries.ext fun n => by
    classical
    simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]
#align mv_polynomial.coe_mul MvPolynomial.coe_mul

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C σ R a :=
  coe_monomial _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.coe_C MvPolynomial.coe_C

set_option linter.deprecated false in
@[simp, norm_cast]
theorem coe_bit0 :
    ((bit0 φ : MvPolynomial σ R) : MvPowerSeries σ R) = bit0 (φ : MvPowerSeries σ R) :=
  coe_add _ _
#align mv_polynomial.coe_bit0 MvPolynomial.coe_bit0

set_option linter.deprecated false in
@[simp, norm_cast]
theorem coe_bit1 :
    ((bit1 φ : MvPolynomial σ R) : MvPowerSeries σ R) = bit1 (φ : MvPowerSeries σ R) := by
  rw [bit1, bit1, coe_add, coe_one, coe_bit0]
#align mv_polynomial.coe_bit1 MvPolynomial.coe_bit1

@[simp, norm_cast]
theorem coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.X s :=
  coe_monomial _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.coe_X MvPolynomial.coe_X

variable (σ R)

theorem coe_injective : Function.Injective (Coe.coe : MvPolynomial σ R → MvPowerSeries σ R) :=
    fun x y h => by
  ext
  simp_rw [← coeff_coe]
  congr
#align mv_polynomial.coe_injective MvPolynomial.coe_injective

variable {σ R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff
#align mv_polynomial.coe_inj MvPolynomial.coe_inj

@[simp]
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]
#align mv_polynomial.coe_eq_zero_iff MvPolynomial.coe_eq_zero_iff

@[simp]
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]
#align mv_polynomial.coe_eq_one_iff MvPolynomial.coe_eq_one_iff

/-- The coercion from multivariable polynomials to multivariable power series
as a ring homomorphism.
-/
def coeToMvPowerSeries.ringHom : MvPolynomial σ R →+* MvPowerSeries σ R where
  toFun := (Coe.coe : MvPolynomial σ R → MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul
#align mv_polynomial.coe_to_mv_power_series.ring_hom MvPolynomial.coeToMvPowerSeries.ringHom

@[simp, norm_cast]
theorem coe_pow (n : ℕ) :
    ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n :=
  coeToMvPowerSeries.ringHom.map_pow _ _
#align mv_polynomial.coe_pow MvPolynomial.coe_pow

variable (φ ψ)

@[simp]
theorem coeToMvPowerSeries.ringHom_apply : coeToMvPowerSeries.ringHom φ = φ :=
  rfl
#align mv_polynomial.coe_to_mv_power_series.ring_hom_apply MvPolynomial.coeToMvPowerSeries.ringHom_apply

section Algebra

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The coercion from multivariable polynomials to multivariable power series
as an algebra homomorphism.
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R →ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map σ (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by simp [algebraMap_apply, MvPowerSeries.algebraMap_apply] }
#align mv_polynomial.coe_to_mv_power_series.alg_hom MvPolynomial.coeToMvPowerSeries.algHom

@[simp]
theorem coeToMvPowerSeries.algHom_apply :
    coeToMvPowerSeries.algHom A φ = MvPowerSeries.map σ (algebraMap R A) ↑φ :=
  rfl
#align mv_polynomial.coe_to_mv_power_series.alg_hom_apply MvPolynomial.coeToMvPowerSeries.algHom_apply

end Algebra

end MvPolynomial

namespace MvPowerSeries

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : MvPowerSeries σ R)

instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A) :=
  RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom
#align mv_power_series.algebra_mv_polynomial MvPowerSeries.algebraMvPolynomial

instance algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A) :=
  (map σ (algebraMap R A)).toAlgebra
#align mv_power_series.algebra_mv_power_series MvPowerSeries.algebraMvPowerSeries

variable (A)

theorem algebraMap_apply' (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ A) p = map σ (algebraMap R A) p :=
  rfl
#align mv_power_series.algebra_map_apply' MvPowerSeries.algebraMap_apply'

theorem algebraMap_apply'' :
    algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f = map σ (algebraMap R A) f :=
  rfl
#align mv_power_series.algebra_map_apply'' MvPowerSeries.algebraMap_apply''

end MvPowerSeries

/-- Formal power series over the coefficient ring `R`.-/
def PowerSeries (R : Type*) :=
  MvPowerSeries Unit R

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section

-- Porting note: not available in Lean 4
-- local reducible PowerSeries


/--
`R⟦X⟧` is notation for `PowerSeries R`,
the semiring of formal power series in one variable over a semiring `R`.
-/
scoped notation:9000 R "⟦X⟧" => PowerSeries R

instance [Inhabited R] : Inhabited R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Zero R] : Zero R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddMonoid R] : AddMonoid R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddGroup R] : AddGroup R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddCommMonoid R] : AddCommMonoid R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [AddCommGroup R] : AddCommGroup R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Semiring R] : Semiring R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [CommSemiring R] : CommSemiring R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Ring R] : Ring R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [CommRing R] : CommRing R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance [Nontrivial R] : Nontrivial R⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance {A} [Semiring R] [AddCommMonoid A] [Module R A] : Module R A⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

instance {A S} [Semiring R] [Semiring S] [AddCommMonoid A] [Module R A] [Module S A] [SMul R S]
    [IsScalarTower R S A] : IsScalarTower R S A⟦X⟧ :=
  Pi.isScalarTower

instance {A} [Semiring A] [CommSemiring R] [Algebra R A] : Algebra R A⟦X⟧ := by
  dsimp only [PowerSeries]
  infer_instance

end

section Semiring

variable (R) [Semiring R]

/-- The `n`th coefficient of a formal power series. -/
def coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R :=
  MvPowerSeries.coeff R (single () n)

/-- The `n`th monomial with coefficient `a` as formal power series. -/
def monomial (n : ℕ) : R →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.monomial R (single () n)

variable {R}

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) : coeff R n = MvPowerSeries.coeff R s := by
  erw [coeff, ← h, ← Finsupp.unique_single s]

/-- Two formal power series are equal if all their coefficients are equal. -/
@[ext]
theorem ext {φ ψ : R⟦X⟧} (h : ∀ n, coeff R n φ = coeff R n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl

/-- Two formal power series are equal if all their coefficients are equal. -/
add_decl_doc PowerSeries.ext_iff

instance [Subsingleton R] : Subsingleton R⟦X⟧ := by
  simp only [subsingleton_iff, PowerSeries.ext_iff]
  subsingleton

/-- Constructor for formal power series. -/
def mk {R} (f : ℕ → R) : R⟦X⟧ := fun s => f (s ())

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff R n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same

theorem coeff_monomial (m n : ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  calc
    coeff R m (monomial R n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]

theorem monomial_eq_mk (n : ℕ) (a : R) : monomial R n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by rw [coeff_monomial, coeff_mk]

@[simp]
theorem coeff_monomial_same (n : ℕ) (a : R) : coeff R n (monomial R n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _

@[simp]
theorem coeff_comp_monomial (n : ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n

variable (R)

/-- The constant coefficient of a formal power series. -/
def constantCoeff : R⟦X⟧ →+* R :=
  MvPowerSeries.constantCoeff Unit R

/-- The constant formal power series. -/
def C : R →+* R⟦X⟧ :=
  MvPowerSeries.C Unit R

variable {R}

/-- The variable of the formal power series ring. -/
def X : R⟦X⟧ :=
  MvPowerSeries.X ()

theorem commute_X (φ : R⟦X⟧) : Commute φ X :=
  MvPowerSeries.commute_X _ _

@[simp]
theorem coeff_zero_eq_constantCoeff : ⇑(coeff R 0) = constantCoeff R := by
  rw [coeff, Finsupp.single_zero]
  rfl

theorem coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff R 0 φ = constantCoeff R φ := by
  rw [coeff_zero_eq_constantCoeff]

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R 0) = C R := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C]

theorem monomial_zero_eq_C_apply (a : R) : monomial R 0 a = C R a := by simp

theorem coeff_C (n : ℕ) (a : R) : coeff R n (C R a : R⟦X⟧) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]

@[simp]
theorem coeff_zero_C (a : R) : coeff R 0 (C R a) = a := by
  rw [coeff_C, if_pos rfl]

theorem coeff_ne_zero_C {a : R} {n : ℕ} (h : n ≠ 0) : coeff R n (C R a) = 0 := by
  rw [coeff_C, if_neg h]

@[simp]
theorem coeff_succ_C {a : R} {n : ℕ} : coeff R (n + 1) (C R a) = 0 :=
  coeff_ne_zero_C n.succ_ne_zero

theorem C_injective : Function.Injective (C R) := by
  intro a b H
  simp_rw [PowerSeries.ext_iff] at H
  simpa only [coeff_zero_C] using H 0

protected theorem subsingleton_iff : Subsingleton R⟦X⟧ ↔ Subsingleton R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b ↦ C_injective (h (C R a) (C R b))

theorem X_eq : (X : R⟦X⟧) = monomial R 1 1 :=
  rfl

theorem coeff_X (n : ℕ) : coeff R n (X : R⟦X⟧) = if n = 1 then 1 else 0 := by
  rw [X_eq, coeff_monomial]

@[simp]
theorem coeff_zero_X : coeff R 0 (X : R⟦X⟧) = 0 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]

@[simp]
theorem coeff_one_X : coeff R 1 (X : R⟦X⟧) = 1 := by rw [coeff_X, if_pos rfl]

@[simp]
theorem X_ne_zero [Nontrivial R] : (X : R⟦X⟧) ≠ 0 := fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff R 1) H

theorem X_pow_eq (n : ℕ) : (X : R⟦X⟧) ^ n = monomial R n 1 :=
  MvPowerSeries.X_pow_eq _ n

theorem coeff_X_pow (m n : ℕ) : coeff R m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff R n ((X : R⟦X⟧) ^ n) = 1 := by
  rw [coeff_X_pow, if_pos rfl]

@[simp]
theorem coeff_one (n : ℕ) : coeff R n (1 : R⟦X⟧) = if n = 0 then 1 else 0 :=
  coeff_C n 1

theorem coeff_zero_one : coeff R 0 (1 : R⟦X⟧) = 1 :=
  coeff_zero_C 1

theorem coeff_mul (n : ℕ) (φ ψ : R⟦X⟧) :
    coeff R n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single, Finset.sum_map]
  rfl

@[simp]
theorem coeff_mul_C (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff R n (φ * C R a) = coeff R n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a

@[simp]
theorem coeff_C_mul (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff R n (C R a * φ) = a * coeff R n φ :=
  MvPowerSeries.coeff_C_mul _ φ a

@[simp]
theorem coeff_smul {S : Type*} [Semiring S] [Module R S] (n : ℕ) (φ : PowerSeries S) (a : R) :
    coeff S n (a • φ) = a • coeff S n φ :=
  rfl

@[simp]
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries S) (a : R) :
    constantCoeff S (a • φ) = a • constantCoeff S φ :=
  rfl

theorem smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C R a * f := by
  ext
  simp

@[simp]
theorem coeff_succ_mul_X (n : ℕ) (φ : R⟦X⟧) : coeff R (n + 1) (φ * X) = coeff R n φ := by
  simp only [coeff, Finsupp.single_add]
  convert φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]

@[simp]
theorem coeff_succ_X_mul (n : ℕ) (φ : R⟦X⟧) : coeff R (n + 1) (X * φ) = coeff R n φ := by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]

@[simp]
theorem constantCoeff_C (a : R) : constantCoeff R (C R a) = a :=
  rfl

@[simp]
theorem constantCoeff_comp_C : (constantCoeff R).comp (C R) = RingHom.id R :=
  rfl

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem constantCoeff_zero : constantCoeff R 0 = 0 :=
  rfl

-- Porting note (#10618): simp can prove this.
-- @[simp]
theorem constantCoeff_one : constantCoeff R 1 = 1 :=
  rfl

@[simp]
theorem constantCoeff_X : constantCoeff R X = 0 :=
  MvPowerSeries.coeff_zero_X _

@[simp]
theorem constantCoeff_mk {f : ℕ → R} : constantCoeff R (mk f) = f 0 := rfl

theorem coeff_zero_mul_X (φ : R⟦X⟧) : coeff R 0 (φ * X) = 0 := by simp

theorem coeff_zero_X_mul (φ : R⟦X⟧) : coeff R 0 (X * φ) = 0 := by simp

theorem constantCoeff_surj : Function.Surjective (constantCoeff R) :=
  fun r => ⟨(C R) r, constantCoeff_C r⟩

-- The following section duplicates the API of `Data.Polynomial.Coeff` and should attempt to keep
-- up to date with that
section

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff R n (C R x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_mul_X_pow (p : R⟦X⟧) (n d : ℕ) :
    coeff R (d + n) (p * X ^ n) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim

@[simp]
theorem coeff_X_pow_mul (p : R⟦X⟧) (n d : ℕ) :
    coeff R (d + n) (X ^ n * p) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (n, d), coeff_X_pow, if_pos rfl, one_mul]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, zero_mul]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_comm, add_right_cancel_iff] at h1
    subst h1
    rfl
  · rw [add_comm]
    exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim

theorem coeff_mul_X_pow' (p : R⟦X⟧) (n d : ℕ) :
    coeff R d (p * X ^ n) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

theorem coeff_X_pow_mul' (p : R⟦X⟧) (n d : ℕ) :
    coeff R d (X ^ n * p) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).ne

end

/-- If a formal power series is invertible, then so is its constant coefficient. -/
theorem isUnit_constantCoeff (φ : R⟦X⟧) (h : IsUnit φ) : IsUnit (constantCoeff R φ) :=
  MvPowerSeries.isUnit_constantCoeff φ h

/-- Split off the constant coefficient. -/
theorem eq_shift_mul_X_add_const (φ : R⟦X⟧) :
    φ = (mk fun p => coeff R (p + 1) φ) * X + C R (constantCoeff R φ) := by
  ext (_ | n)
  · simp only [coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      mul_zero, coeff_zero_C, zero_add]
  · simp only [coeff_succ_mul_X, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero,
      if_false, add_zero]

/-- Split off the constant coefficient. -/
theorem eq_X_mul_shift_add_const (φ : R⟦X⟧) :
    φ = (X * mk fun p => coeff R (p + 1) φ) + C R (constantCoeff R φ) := by
  ext (_ | n)
  · simp only [coeff_zero_eq_constantCoeff, map_add, map_mul, constantCoeff_X,
      zero_mul, coeff_zero_C, zero_add]
  · simp only [coeff_succ_X_mul, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero,
      if_false, add_zero]

section Map

variable {S : Type*} {T : Type*} [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients. -/
def map : R⟦X⟧ →+* S⟦X⟧ :=
  MvPowerSeries.map _ f

@[simp]
theorem map_id : (map (RingHom.id R) : R⟦X⟧ → R⟦X⟧) = id :=
  rfl

theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
theorem coeff_map (n : ℕ) (φ : R⟦X⟧) : coeff S n (map f φ) = f (coeff R n φ) :=
  rfl

@[simp]
theorem map_C (r : R) : map f (C _ r) = C _ (f r) := by
  ext
  simp [coeff_C, apply_ite f]

@[simp]
theorem map_X : map f X = X := by
  ext
  simp [coeff_X, apply_ite f]

end Map

theorem X_pow_dvd_iff {n : ℕ} {φ : R⟦X⟧} :
    (X : R⟦X⟧) ^ n ∣ φ ↔ ∀ m, m < n → coeff R m φ = 0 := by
  convert@MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm

theorem X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantCoeff R φ = 0 := by
  rw [← pow_one (X : R⟦X⟧), X_pow_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]

end Semiring

section CommSemiring

variable [CommSemiring R]

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def rescale (a : R) : R⟦X⟧ →+* R⟦X⟧ where
  toFun f := PowerSeries.mk fun n => a ^ n * PowerSeries.coeff R n f
  map_zero' := by
    ext
    simp only [LinearMap.map_zero, PowerSeries.coeff_mk, mul_zero]
  map_one' := by
    ext1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, pow_zero a]
    rfl
  map_add' := by
    intros
    ext
    dsimp only
    exact mul_add _ _ _
  map_mul' f g := by
    ext
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
    apply sum_congr rfl
    simp only [coeff_mk, Prod.forall, mem_antidiagonal]
    intro b c H
    rw [← H, pow_add, mul_mul_mul_comm]

@[simp]
theorem coeff_rescale (f : R⟦X⟧) (a : R) (n : ℕ) :
    coeff R n (rescale a f) = a ^ n * coeff R n f :=
  coeff_mk n (fun n ↦ a ^ n * (coeff R n) f)

@[simp]
theorem rescale_zero : rescale 0 = (C R).comp (constantCoeff R) := by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    PowerSeries.coeff_mk _ _, coeff_C]
  split_ifs with h <;> simp [h]

theorem rescale_zero_apply : rescale 0 X = C R (constantCoeff R X) := by simp

@[simp]
theorem rescale_one : rescale 1 = RingHom.id R⟦X⟧ := by
  ext
  simp only [coeff_rescale, one_pow, one_mul, RingHom.id_apply]

theorem rescale_mk (f : ℕ → R) (a : R) : rescale a (mk f) = mk fun n : ℕ => a ^ n * f n := by
  ext
  rw [coeff_rescale, coeff_mk, coeff_mk]

theorem rescale_rescale (f : R⟦X⟧) (a b : R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow, mul_comm _ (b ^ n), mul_assoc]

theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]

end CommSemiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]

/-- Coefficients of a product of power series -/
theorem coeff_prod (f : ι → PowerSeries R) (d : ℕ) (s : Finset ι) :
    coeff R d (∏ j ∈ s, f j) = ∑ l ∈ finsuppAntidiag s d, ∏ i ∈ s, coeff R (l i) (f i) := by
  simp only [coeff]
  rw [MvPowerSeries.coeff_prod, ← AddEquiv.finsuppUnique_symm d, ← mapRange_finsuppAntidiag_eq,
    sum_map, sum_congr rfl]
  intro x _
  apply prod_congr rfl
  intro i _
  congr 2
  simp only [AddEquiv.toEquiv_eq_coe, Finsupp.mapRange.addEquiv_toEquiv, AddEquiv.toEquiv_symm,
    Equiv.coe_toEmbedding, Finsupp.mapRange.equiv_apply, AddEquiv.coe_toEquiv_symm,
    Finsupp.mapRange_apply, AddEquiv.finsuppUnique_symm]

/-- The `n`-th coefficient of the `k`-th power of a power series. -/
lemma coeff_pow (k n : ℕ) (φ : R⟦X⟧) :
    coeff R n (φ ^ k) = ∑ l ∈ finsuppAntidiag (range k) n, ∏ i ∈ range k, coeff R (l i) φ := by
  have h₁ (i : ℕ) : Function.const ℕ φ i = φ := rfl
  have h₂ (i : ℕ) : ∏ j ∈ range i, Function.const ℕ φ j = φ ^ i := by
    apply prod_range_induction (fun _ => φ) (fun i => φ ^ i) rfl (congrFun rfl) i
  rw [← h₂, ← h₁ k]
  apply coeff_prod (f := Function.const ℕ φ) (d := n) (s := range k)

/-- First coefficient of the product of two power series. -/
lemma coeff_one_mul (φ ψ : R⟦X⟧) : coeff R 1 (φ * ψ) =
    coeff R 1 φ * constantCoeff R ψ + coeff R 1 ψ * constantCoeff R φ := by
  have : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
  rw [coeff_mul, this, Finset.sum_insert, Finset.sum_singleton, coeff_zero_eq_constantCoeff,
    mul_comm, add_comm]
  norm_num

/-- First coefficient of the `n`-th power of a power series. -/
lemma coeff_one_pow (n : ℕ) (φ : R⟦X⟧) :
    coeff R 1 (φ ^ n) = n * coeff R 1 φ * (constantCoeff R φ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn)
  · simp
  induction n with
  | zero => by_contra; linarith
  | succ n' ih =>
      have h₁ (m : ℕ) : φ ^ (m + 1) = φ ^ m * φ := by exact rfl
      have h₂ : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
      rw [h₁, coeff_mul, h₂, Finset.sum_insert, Finset.sum_singleton]
      · simp only [coeff_zero_eq_constantCoeff, map_pow, Nat.cast_add, Nat.cast_one,
          add_tsub_cancel_right]
        have h₀ : n' = 0 ∨ 1 ≤ n' := by omega
        rcases h₀ with h' | h'
        · by_contra h''
          rw [h'] at h''
          simp only [pow_zero, one_mul, coeff_one, one_ne_zero, ↓reduceIte, zero_mul, add_zero,
            CharP.cast_eq_zero, zero_add, mul_one, not_true_eq_false] at h''
          norm_num at h''
        · rw [ih]
          · conv => lhs; arg 2; rw [mul_comm, ← mul_assoc]
            move_mul [← (constantCoeff R) φ ^ (n' - 1)]
            conv => enter [1, 2, 1, 1, 2]; rw [← pow_one (a := constantCoeff R φ)]
            rw [← pow_add (a := constantCoeff R φ)]
            conv => enter [1, 2, 1, 1]; rw [Nat.sub_add_cancel h']
            conv => enter [1, 2, 1]; rw [mul_comm]
            rw [mul_assoc, ← one_add_mul, add_comm, mul_assoc]
            conv => enter [1, 2]; rw [mul_comm]
          exact h'
      · decide

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A]

theorem not_isField : ¬IsField A⟦X⟧ := by
  by_cases hA : Subsingleton A
  · exact not_isField_of_subsingleton _
  · nontriviality A
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    use Ideal.span {X}
    constructor
    · rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact X_ne_zero
    · rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
        X_dvd_iff, constantCoeff_one]
      exact one_ne_zero

@[simp]
theorem rescale_X (a : A) : rescale a X = C A a * X := by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]

theorem rescale_neg_one_X : rescale (-1 : A) X = -X := by
  rw [rescale_X, map_neg, map_one, neg_one_mul]

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
noncomputable def evalNegHom : A⟦X⟧ →+* A⟦X⟧ :=
  rescale (-1 : A)

@[simp]
theorem evalNegHom_X : evalNegHom (X : A⟦X⟧) = -X :=
  rescale_neg_one_X

end CommRing

section Domain

variable [Ring R]

theorem eq_zero_or_eq_zero_of_mul_eq_zero [NoZeroDivisors R] (φ ψ : R⟦X⟧) (h : φ * ψ = 0) :
    φ = 0 ∨ ψ = 0 := by
  classical
  rw [or_iff_not_imp_left]
  intro H
  have ex : ∃ m, coeff R m φ ≠ 0 := by
    contrapose! H
    exact ext H
  let m := Nat.find ex
  have hm₁ : coeff R m φ ≠ 0 := Nat.find_spec ex
  have hm₂ : ∀ k < m, ¬coeff R k φ ≠ 0 := fun k => Nat.find_min ex
  ext n
  rw [(coeff R n).map_zero]
  induction' n using Nat.strong_induction_on with n ih
  replace h := congr_arg (coeff R (m + n)) h
  rw [LinearMap.map_zero, coeff_mul, Finset.sum_eq_single (m, n)] at h
  · replace h := NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h
    rw [or_iff_not_imp_left] at h
    exact h hm₁
  · rintro ⟨i, j⟩ hij hne
    by_cases hj : j < n
    · rw [ih j hj, mul_zero]
    by_cases hi : i < m
    · specialize hm₂ _ hi
      push_neg at hm₂
      rw [hm₂, zero_mul]
    rw [mem_antidiagonal] at hij
    push_neg at hi hj
    suffices m < i by
      have : m + n < i + j := add_lt_add_of_lt_of_le this hj
      exfalso
      exact ne_of_lt this hij.symm
    contrapose! hne
    obtain rfl := le_antisymm hi hne
    simpa [Ne, Prod.mk.inj_iff] using (add_right_inj m).mp hij
  · contrapose!
    intro
    rw [mem_antidiagonal]

instance [NoZeroDivisors R] : NoZeroDivisors R⟦X⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero _ _

instance [IsDomain R] : IsDomain R⟦X⟧ :=
  NoZeroDivisors.to_isDomain _

end Domain

section IsDomain

variable [CommRing R] [IsDomain R]

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal. -/
theorem span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧)).IsPrime := by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker (constantCoeff R) by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- The variable of the power series ring over an integral domain is prime. -/
theorem X_prime : Prime (X : R⟦X⟧) := by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff R 1)] using congr_arg (coeff R 1) h

/-- The variable of the power series ring over an integral domain is irreducible. -/
theorem X_irreducible : Irreducible (X : R⟦X⟧) := X_prime.irreducible

theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rw [coeff_rescale, coeff_rescale, mul_eq_mul_left_iff] at h
  apply h.resolve_right
  intro h'
  exact ha (pow_eq_zero h')

end IsDomain

section Algebra

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem C_eq_algebraMap {r : R} : C R r = (algebraMap R R⟦X⟧) r :=
  rfl

theorem algebraMap_apply {r : R} : algebraMap R A⟦X⟧ r = C A (algebraMap R A r) :=
  MvPowerSeries.algebraMap_apply

instance [Nontrivial R] : Nontrivial (Subalgebra R R⟦X⟧) :=
  { inferInstanceAs <| Nontrivial <| Subalgebra R <| MvPowerSeries Unit R with }

end Algebra

end PowerSeries

namespace Polynomial

open Finsupp Polynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] (φ ψ : R[X])

-- Porting note: added so we can add the `@[coe]` attribute
/-- The natural inclusion from polynomials into formal power series. -/
@[coe]
def ToPowerSeries : R[X] → (PowerSeries R) := fun φ =>
  PowerSeries.mk fun n => coeff φ n

/-- The natural inclusion from polynomials into formal power series. -/
instance coeToPowerSeries : Coe R[X] (PowerSeries R) :=
  ⟨ToPowerSeries⟩

theorem coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ) :=
  rfl

@[simp, norm_cast]
theorem coeff_coe (n) : PowerSeries.coeff R n φ = coeff φ n :=
  congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]
theorem coe_monomial (n : ℕ) (a : R) :
    (monomial n a : PowerSeries R) = PowerSeries.monomial R n a := by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, norm_cast]
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  simp

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
theorem coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C R a := by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
theorem coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X :=
  coe_monomial _ _

@[simp]
theorem constantCoeff_coe : PowerSeries.constantCoeff R φ = φ.coeff 0 :=
  rfl

variable (R)

theorem coe_injective : Function.Injective (Coe.coe : R[X] → PowerSeries R) := fun x y h => by
  ext
  simp_rw [← coeff_coe]
  congr

variable {R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff

@[simp]
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

variable (φ ψ)

/-- The coercion from polynomials to power series
as a ring homomorphism.
-/
def coeToPowerSeries.ringHom : R[X] →+* PowerSeries R where
  toFun := (Coe.coe : R[X] → PowerSeries R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]
theorem coeToPowerSeries.ringHom_apply : coeToPowerSeries.ringHom φ = φ :=
  rfl

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n :=
  coeToPowerSeries.ringHom.map_pow _ _

theorem eval₂_C_X_eq_coe : φ.eval₂ (PowerSeries.C R) PowerSeries.X = ↑φ := by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply, eval₂_eq_sum_range, eval₂_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul, map_pow, coeToPowerSeries.ringHom_apply,
    coeToPowerSeries.ringHom_apply, coe_C, coe_X]

variable (A : Type*) [Semiring A] [Algebra R A]

/-- The coercion from polynomials to power series
as an algebra homomorphism.
-/
def coeToPowerSeries.algHom : R[X] →ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

@[simp]
theorem coeToPowerSeries.algHom_apply :
    coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl

end Polynomial

namespace PowerSeries

section Algebra

open Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : R⟦X⟧)

instance algebraPolynomial : Algebra R[X] A⟦X⟧ :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom

instance algebraPowerSeries : Algebra R⟦X⟧ A⟦X⟧ :=
  (map (algebraMap R A)).toAlgebra

-- see Note [lower instance priority]
instance (priority := 100) algebraPolynomial' {A : Type*} [CommSemiring A] [Algebra R A[X]] :
    Algebra R A⟦X⟧ :=
  RingHom.toAlgebra <| Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R A[X])

variable (A)

theorem algebraMap_apply' (p : R[X]) : algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p :=
  rfl

theorem algebraMap_apply'' :
    algebraMap R⟦X⟧ A⟦X⟧ f = map (algebraMap R A) f :=
  rfl

end Algebra

end PowerSeries

end
