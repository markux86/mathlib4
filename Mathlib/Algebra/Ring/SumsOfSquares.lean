/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Sums of squares

We introduce a predicate for sums of squares in a ring.

## Main declarations

- `IsSumSq : R → Prop`: for a type `R` with addition, multiplication and a zero,
  an inductive predicate defining the property of being a sum of squares in `R`.
  `0 : R` is a sum of squares and if `S` is a sum of squares, then, for all `a : R`,
  `a * a + s` is a sum of squares.
- `AddMonoid.sumSq R`: the submonoid of sums of squares in an additive monoid `R`
  with multiplication.

-/

variable {R : Type*}

/--
The property of being a sum of squares is defined inductively by:
`0 : R` is a sum of squares and if `s : R` is a sum of squares,
then for all `a : R`, `a * a + s` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                                    : IsSumSq 0
  | sq_add (a : R) {s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)

@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq

/--
In an additive monoid with multiplication,
if `s₁` and `s₂` are sums of squares, then `s₁ + s₂` is a sum of squares.
-/
theorem IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [add_assoc, sq_add]

@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {s : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, `AddSubmonoid.sumSq R` is the submonoid of sums of
squares in `R`.
-/
@[simps]
def sumSq [AddMonoid T] : AddSubmonoid T where
  carrier   := {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem'  := .add

attribute [norm_cast] coe_sumSq

@[simp] theorem mem_sumSq : s ∈ sumSq T ↔ IsSumSq s := Iff.rfl

end AddSubmonoid

@[deprecated (since := "2024-08-09")] alias SumSqIn := AddSubmonoid.sumSq
@[deprecated (since := "2025-01-03")] alias sumSqIn := AddSubmonoid.sumSq
@[deprecated (since := "2025-01-06")] alias sumSq := AddSubmonoid.sumSq

/--
In an additive monoid with multiplication, squares are sums of squares
(see Mathlib.Algebra.Group.Even).
-/
theorem mem_sumSq_of_isSquare [AddMonoid R] [Mul R] {x : R} (hx : IsSquare x) :
    x ∈ AddSubmonoid.sumSq R := by
  rcases hx with ⟨y, hy⟩
  rw [hy, ← AddMonoid.add_zero (y * y)]
  exact IsSumSq.sq_add _ IsSumSq.zero

@[deprecated (since := "2024-08-09")] alias SquaresInSumSq := mem_sumSq_of_isSquare
@[deprecated (since := "2025-01-03")] alias mem_sumSqIn_of_isSquare := mem_sumSq_of_isSquare

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSq R := by
  refine le_antisymm (closure_le.2 (fun x hx ↦ mem_sumSq_of_isSquare hx)) (fun x hx ↦ ?_)
  induction hx <;> aesop

@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare

/--
In an additive commutative monoid with multiplication,
`∑ i ∈ I, a i * a i` is a sum of squares.
-/
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i * a i) := by
  induction I using Finset.cons_induction with
  | empty         => simpa using IsSumSq.zero
  | cons i _ hi h => exact (Finset.sum_cons (β := R) hi) ▸ IsSumSq.sq_add (a i) h

@[deprecated (since := "2024-12-27")] alias isSumSq_sum_mul_self := IsSumSq.sum_mul_self

/--
In a linearly ordered semiring with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`),
sums of squares are non-negative.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {s : R}
    (hs : IsSumSq s) : 0 ≤ s := by
  induction hs with
  | zero           => simp only [le_refl]
  | sq_add x _ ih  => apply add_nonneg ?_ ih; simp only [← pow_two x, sq_nonneg]

@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg
