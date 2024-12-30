/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Isaacs
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Algebraic Closure

In this file we construct the algebraic closure of a field

## Main Definitions

- `AlgebraicClosure k` is an algebraic closure of `k` (in the same universe).
  It is constructed by taking the polynomial ring generated by indeterminates `x_f`
  corresponding to monic irreducible polynomials `f` with coefficients in `k`, and quotienting
  out by a maximal ideal containing every `f(x_f)`. Usually this needs to be repeated countably
  many times (see Exercise 1.13 in [atiyah-macdonald]), but using a theorem of Isaacs [Isaacs1980],
  once is enough (see https://kconrad.math.uconn.edu/blurbs/galoistheory/algclosure.pdf).

## Tags

algebraic closure, algebraically closed
-/

universe u v w

noncomputable section

open Polynomial

variable (k : Type u) [Field k]

namespace AlgebraicClosure

open MvPolynomial

/-- The subtype of monic irreducible polynomials -/
abbrev MonicIrreducible : Type u :=
  { f : k[X] // Monic f ∧ Irreducible f }

/-- Sends a monic irreducible polynomial `f` to `f(x_f)` where `x_f` is a formal indeterminate. -/
def evalXSelf (f : MonicIrreducible k) : MvPolynomial (MonicIrreducible k) k :=
  Polynomial.eval₂ MvPolynomial.C (X f) f

/-- The span of `f(x_f)` across monic irreducible polynomials `f` where `x_f` is an
indeterminate. -/
def spanEval : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Ideal.span <| Set.range <| evalXSelf k

open Classical in
/-- Given a finset of monic irreducible polynomials, construct an algebra homomorphism to the
splitting field of the product of the polynomials sending each indeterminate `x_f` represented by
the polynomial `f` in the finset to a root of `f`. -/
def toSplittingField (s : Finset (MonicIrreducible k)) :
    MvPolynomial (MonicIrreducible k) k →ₐ[k] SplittingField (∏ x ∈ s, x : k[X]) :=
  MvPolynomial.aeval fun f =>
    if hf : f ∈ s then
      rootOfSplits _
        ((splits_prod_iff _ fun (j : MonicIrreducible k) _ => j.2.2.ne_zero).1
          (SplittingField.splits _) f hf)
        (mt isUnit_iff_degree_eq_zero.2 f.2.2.not_unit)
    else 37

theorem toSplittingField_evalXSelf {s : Finset (MonicIrreducible k)} {f} (hf : f ∈ s) :
    toSplittingField k s (evalXSelf k f) = 0 := by
  rw [toSplittingField, evalXSelf, ← AlgHom.coe_toRingHom, hom_eval₂, AlgHom.coe_toRingHom,
    MvPolynomial.aeval_X, dif_pos hf, ← MvPolynomial.algebraMap_eq, AlgHom.comp_algebraMap]
  exact map_rootOfSplits _ _ _

theorem spanEval_ne_top : spanEval k ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one, spanEval, Ideal.span, ← Set.image_univ,
    Finsupp.mem_span_image_iff_linearCombination]
  rintro ⟨v, _, hv⟩
  replace hv := congr_arg (toSplittingField k v.support) hv
  rw [map_one, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_eq_zero] at hv
  · exact zero_ne_one hv
  intro j hj
  rw [smul_eq_mul, map_mul, toSplittingField_evalXSelf _ (s := v.support) hj,
    mul_zero]

/-- A random maximal ideal that contains `spanEval k` -/
def maxIdeal : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Classical.choose <| Ideal.exists_le_maximal _ <| spanEval_ne_top k

instance maxIdeal.isMaximal : (maxIdeal k).IsMaximal :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanEval_ne_top k).1

theorem le_maxIdeal : spanEval k ≤ maxIdeal k :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanEval_ne_top k).2

end AlgebraicClosure

open AlgebraicClosure in
/-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for
each polynomial over the field. -/
@[stacks 09GT]
def AlgebraicClosure : Type u :=
  MvPolynomial (MonicIrreducible k) k ⧸ maxIdeal k

namespace AlgebraicClosure

instance instCommRing : CommRing (AlgebraicClosure k) := Ideal.Quotient.commRing _
instance instInhabited : Inhabited (AlgebraicClosure k) := ⟨37⟩

instance {S : Type*} [DistribSMul S k] [IsScalarTower S k k] : SMul S (AlgebraicClosure k) :=
  Submodule.Quotient.instSMul' _

instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R k] : Algebra R (AlgebraicClosure k) :=
  Ideal.Quotient.algebra _

instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Algebra S k] [Algebra R k]
    [IsScalarTower R S k] : IsScalarTower R S (AlgebraicClosure k) :=
  Ideal.Quotient.isScalarTower _ _ _

instance instGroupWithZero : GroupWithZero (AlgebraicClosure k) where
  __ := Ideal.Quotient.field _

instance instField : Field (AlgebraicClosure k) where
  __ := instCommRing _
  __ := instGroupWithZero _
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast q := algebraMap k _ q
  ratCast q := algebraMap k _ q
  nnratCast_def q := by change algebraMap k _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap k _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  nnqsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

instance isAlgebraic : Algebra.IsAlgebraic k (AlgebraicClosure k) :=
  ⟨fun z =>
    IsIntegral.isAlgebraic <| by
      let ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z
      rw [← hp]
      induction p using MvPolynomial.induction_on generalizing z with
        | h_C => exact isIntegral_algebraMap
        | h_add _ _ ha hb => exact (ha _ rfl).add (hb _ rfl)
        | h_X p f ih =>
          refine @IsIntegral.mul k _ _ _ _ _ (Ideal.Quotient.mk (maxIdeal k) _) (ih _ rfl) ?_
          refine ⟨f, f.2.1, ?_⟩
          erw [algebraMap, ← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
          exact le_maxIdeal k (Ideal.subset_span ⟨f, rfl⟩)⟩

instance : IsAlgClosure k (AlgebraicClosure k) := .of_exist_roots fun f hfm hfi ↦
  ⟨Ideal.Quotient.mk _ <| MvPolynomial.X (⟨f, hfm, hfi⟩ : MonicIrreducible k), by
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [aeval_def, ← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact le_maxIdeal k (Ideal.subset_span <| ⟨_, rfl⟩)⟩

instance isAlgClosed : IsAlgClosed (AlgebraicClosure k) := IsAlgClosure.isAlgClosed k

instance [CharZero k] : CharZero (AlgebraicClosure k) :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (AlgebraicClosure k)))

instance {p : ℕ} [CharP k p] : CharP (AlgebraicClosure k) p :=
  charP_of_injective_algebraMap (RingHom.injective (algebraMap k (AlgebraicClosure k))) p

instance {L : Type*} [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    IsAlgClosure k (AlgebraicClosure L) where
  isAlgebraic := .trans (L := L)
  isAlgClosed := inferInstance

end AlgebraicClosure
