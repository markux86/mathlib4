/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Sums of squares

We introduce sums of squares in a type `R` endowed with an `[Add R]`, `[Zero R]` and `[Mul R]`
instances. Sums of squares in `R` are defined by an inductive predicate `IsSumSq : R → Prop`:
`0 : R` is a sum of squares and if `S` is a sum of squares, then for all `a : R`, `a * a + S` is a
sum of squares in `R`.

## Declarations

- The predicate `IsSumSq : R → Prop`, defining the property of being a sum of squares in `R`.
- The terms `AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` :
in an additive monoid with multiplication `R` and a semiring `R`, we introduce the terms
`AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` as the submonoid and subsemiring, respectively,
of `R` whose carrier is the subset `{S : R | IsSumSq S}`.

-/

universe u
variable {R : Type*}

/--
In a type `R` with an addition, a zero element and a multiplication, the property of being a sum of
squares is defined by an inductive predicate: `0 : R` is a sum of squares and if `S` is a sum of
squares, then for all `a : R`, `a * a + S` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add {a S : R} (hS : IsSumSq S) : IsSumSq (a * a + S)

@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq

/-- Alternative induction scheme for `IsSumSq` using `IsSquare`. -/
def IsSumSq.inductionOn' [Mul R] [Add R] [Zero R]
    {p : (S : R) → (h : IsSumSq S) → Prop} {S : R} (hS : IsSumSq S)
    (zero : p 0 zero)
    (sq_add : ∀ {x S}, (hS : IsSumSq S) → (hx : IsSquare x) → p S hS →
      p (x + S) (by rcases hx with ⟨_, rfl⟩; exact sq_add hS)) : p S hS :=
  match hS with
  | .zero         => zero
  | .sq_add hS_ih => sq_add hS_ih (.mul_self _) (inductionOn' hS_ih zero sq_add)

/-- In an additive monoid with multiplication,
if `S₁` and `S₂` are sums of squares, then `S₁ + S₂` is a sum of squares. -/
@[aesop unsafe 90% apply]
theorem IsSumSq.add [AddMonoid R] [Mul R] {S₁ S₂ : R}
    (h₁ : IsSumSq S₁) (h₂ : IsSumSq S₂) : IsSumSq (S₁ + S₂) := by
  induction h₁ with
  | zero        => simp_all
  | sq_add _ ih => simp_all [add_assoc, sq_add]

@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {a : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, the type `AddSubmonoid.sumSqIn R`
is the submonoid of sums of squares in `R`.
-/
def sumSqIn : AddSubmonoid T where
  carrier := {S : T | IsSumSq S}
  zero_mem' := IsSumSq.zero
  add_mem' := IsSumSq.add

@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end AddSubmonoid

/-- In an additive, commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares. -/
@[aesop unsafe 90% apply]
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {S : ι → R}
    (hS : ∀ i ∈ I, IsSumSq <| S i) : IsSumSq (∑ i ∈ I, S i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSqIn R) hS

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  rw [← add_zero (a * a)]; exact sq_add zero

/-- In an additive unital magma with multiplication `R`, squares in `R` are sums of squares.
By definition, a square in `R` is a term `x : R` such that `x = y * y` for some `y : R`
and in Mathlib this is known as `IsSquare R` (see Mathlib.Algebra.Group.Even). -/
@[aesop unsafe 50% apply]
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) :
    IsSumSq x := by rcases hx with ⟨_, rfl⟩; apply IsSumSq.mul_self

/-- A term of the form `∑ i ∈ I, x i`, where each `x i` is a square, satisfies `IsSumSq`. -/
@[aesop safe apply]
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R]
    {ι : Type*} {I : Finset ι} (x : ι → R) : IsSumSq (∑ i ∈ I, x i * x i) := sum (by aesop)

@[deprecated (since := "2024-12-23")] alias isSumSq_sum_mul_self := IsSumSq.sum_mul_self

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx with
  | zero         => exact zero_mem _
  | sq_add _ ih  => exact add_mem (subset_closure (.mul_self _)) ih

@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare

/-- A term of `R` satisfying `IsSumSq` can be written as `∑ i ∈ I, x i`
where each `x i` is a square in `R`. -/
theorem IsSumSq.exists_sum [AddCommMonoid R] [Mul R] {a : R} (ha : IsSumSq a) :
    (∃ (ι : Type) (I : Finset ι) (x : ι → R), (∀ i ∈ I, IsSquare (x i)) ∧ ∑ i ∈ I, x i = a) :=
  AddSubmonoid.exists_finset_sum_of_mem_closure (s := {x : R | IsSquare x}) (by simpa)

/-- Universe-polymorphic version of `exists_sum`. -/
theorem IsSumSq.exists_sum' [AddCommMonoid R] [Mul R] {a : R} (ha : IsSumSq a) :
    (∃ (ι : Type u) (I : Finset ι) (x : ι → R), (∀ i ∈ I, IsSquare (x i)) ∧ ∑ i ∈ I, x i = a) := by
  rcases exists_sum ha with ⟨ι, I, x, _⟩
  exact ⟨ULift.{u} ι, .map (Equiv.ulift.symm.toEmbedding) I, x ∘ (Equiv.ulift.toEmbedding),
    by simpa⟩

/-- A term of `R` satisfies `IsSumSq` if and only if it can be written as `∑ i ∈ I, x i`
where each `x i` is a square in `R`. -/
theorem isSumSq_iff_exists_sum [AddCommMonoid R] [Mul R] (a : R) :
    IsSumSq a ↔
    (∃ (ι : Type) (I : Finset ι) (x : ι → R), (∀ i ∈ I, IsSquare (x i)) ∧ ∑ i ∈ I, x i = a) :=
  ⟨IsSumSq.exists_sum, by aesop⟩

/-- A term of `R` satisfying `IsSumSq` can be written as `∑ i ∈ I, x i * x i`. -/
theorem IsSumSq.exists_sum_mul_self [AddCommMonoid R] [Mul R] {a : R} (ha : IsSumSq a) :
    (∃ (ι : Type) (I : Finset ι) (x : ι → R), a = ∑ i ∈ I, x i * x i) := by
  rcases exists_sum ha with ⟨_, I, _, y_cl, rfl⟩
  choose! x hx using y_cl
  exact ⟨_, I, x, Finset.sum_equiv (by rfl) (by simp) hx⟩

/-- Universe-polymorphic version of `exists_sum_mul_self_of_isSumSq`. -/
theorem IsSumSq.exists_sum_mul_self' [AddCommMonoid R] [Mul R] {a : R} (ha : IsSumSq a) :
    (∃ (ι : Type u) (I : Finset ι) (x : ι → R), a = ∑ i ∈ I, x i * x i) := by
  obtain ⟨ι, I, x, _⟩ := exists_sum_mul_self ha
  exact ⟨ULift.{u} ι, .map (Equiv.ulift.symm.toEmbedding) I, x ∘ (Equiv.ulift.toEmbedding),
    by simpa⟩

/-- A term of `R` satisfies `IsSumSq` if and only if it can be written as `∑ i ∈ I, x i * x i`. -/
theorem isSumSq_iff_exists_sum_mul_self [AddCommMonoid R] [Mul R] (a : R) :
    IsSumSq a ↔
    (∃ (ι : Type) (I : Finset ι) (x : ι → R), a = ∑ i ∈ I, x i * x i) := by
  refine ⟨IsSumSq.exists_sum_mul_self, by rintro ⟨_, _, _, rfl⟩; apply IsSumSq.sum_mul_self⟩

/-- In a (not necessarily unital) commutative semiring,
if `S₁` and `S₂` are sums of squares, then `S₁ * S₂` is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.mul [NonUnitalCommSemiring R] {S₁ S₂ : R}
    (h₁ : IsSumSq S₁) (h₂ : IsSumSq S₂) : IsSumSq (S₁ * S₂) := by
  rw [isSumSq_iff_exists_sum] at *
  rcases h₁, h₂ with ⟨⟨ι, I, x, hx, rfl⟩, ⟨β, J, y, hy, rfl⟩⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  exact ⟨_, I ×ˢ J, fun ⟨i,j⟩ => x i * y j, by aesop (add safe IsSquare.mul)⟩

namespace Subsemiring
variable {T : Type*} [CommSemiring T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : Subsemiring T where
  __ := AddSubmonoid.sumSqIn T
  mul_mem' := IsSumSq.mul
  one_mem' := IsSquare.isSumSq isSquare_one

@[simp] lemma sumSqIn_toAddSubmonoid : (sumSqIn T).toAddSubmonoid = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares
is a sum of squares. -/
@[aesop unsafe 50% apply]
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ I, IsSumSq <| f i) : IsSumSq (∏ i ∈ I, f i) := by
  simpa using prod_mem (S := Subsemiring.sumSqIn R) hf

/--
In a commutative semiring `R`, the subsemiring generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
theorem Subsemiring.closure_isSquare [CommSemiring R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine closure_eq_of_le (fun x hx => IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  rcases IsSumSq.exists_sum hx with ⟨_, _, _, _, rfl⟩
  exact sum_mem (by aesop)

/--
Let `R` be a linearly ordered semiring in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used in
`Mathlib.Algebra.Ring.Semireal.Defs` to show that such semirings are semireal.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : IsSumSq S) : 0 ≤ S := by
  rcases IsSumSq.exists_sum_mul_self pS with ⟨_, _, x, rfl⟩
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg
