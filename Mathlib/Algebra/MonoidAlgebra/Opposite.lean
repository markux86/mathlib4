/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

assert_not_exists AlgEquiv
assert_not_exists NonUnitalAlgHom

noncomputable section

variable {k G : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

section Opposite

open Finsupp MulOpposite

variable [Semiring k]

/-- The opposite of a `MonoidAlgebra R I` equivalent as a ring to
the `MonoidAlgebra Rᵐᵒᵖ Iᵐᵒᵖ` over the opposite ring, taking elements to their opposite. -/
@[simps! (config := { simpRhs := true }) apply symm_apply]
protected noncomputable def opRingEquiv [Monoid G] :
    (MonoidAlgebra k G)ᵐᵒᵖ ≃+* MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ :=
  { opAddEquiv.symm.trans <|
      (Finsupp.mapRange.addEquiv (opAddEquiv : k ≃+ kᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv with
    map_mul' := by
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe]; erw [AddEquiv.coe_toEquiv]
      rw [← AddEquiv.coe_toAddMonoidHom]
      refine Iff.mpr (AddMonoidHom.map_mul_iff (R := (MonoidAlgebra k G)ᵐᵒᵖ)
        (S := MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ) _) ?_
      ext
      -- Porting note: `reducible` cannot be `local` so proof gets long.
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, opAddEquiv_apply,
        Function.comp_apply, singleAddHom_apply, AddMonoidHom.compr₂_apply, AddMonoidHom.coe_mul,
        AddMonoidHom.coe_mulLeft, AddMonoidHom.compl₂_apply]
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
        AddEquiv.trans_apply, AddEquiv.trans_apply, MulOpposite.opAddEquiv_symm_apply]
      rw [MulOpposite.unop_mul (α := MonoidAlgebra k G), unop_op, unop_op, single_mul_single]
      simp }

-- @[simp] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10618): simp can prove this.
-- More specifically, the LHS simplifies to `Finsupp.single`, which implies there's some
-- defeq abuse going on.
theorem opRingEquiv_single [Monoid G] (r : k) (x : G) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by simp

theorem opRingEquiv_symm_single [Monoid G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by simp

end Opposite

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

section Opposite

open Finsupp MulOpposite

variable [Semiring k]

/-- The opposite of an `R[I]` is ring equivalent to
the `AddMonoidAlgebra Rᵐᵒᵖ I` over the opposite ring, taking elements to their opposite. -/
@[simps! (config := { simpRhs := true }) apply symm_apply]
protected noncomputable def opRingEquiv [AddCommMonoid G] :
    k[G]ᵐᵒᵖ ≃+* kᵐᵒᵖ[G] :=
  { MulOpposite.opAddEquiv.symm.trans
      (Finsupp.mapRange.addEquiv (MulOpposite.opAddEquiv : k ≃+ kᵐᵒᵖ)) with
    map_mul' := by
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe]; erw [AddEquiv.coe_toEquiv]
      rw [← AddEquiv.coe_toAddMonoidHom]
      refine Iff.mpr (AddMonoidHom.map_mul_iff (R := k[G]ᵐᵒᵖ) (S := kᵐᵒᵖ[G]) _) ?_
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Was `ext`.
      refine AddMonoidHom.mul_op_ext _ _ <| addHom_ext' fun i₁ => AddMonoidHom.ext fun r₁ =>
        AddMonoidHom.mul_op_ext _ _ <| addHom_ext' fun i₂ => AddMonoidHom.ext fun r₂ => ?_
      -- Porting note: `reducible` cannot be `local` so proof gets long.
      dsimp
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
        MulOpposite.opAddEquiv_symm_apply]; rw [MulOpposite.unop_mul (α := k[G])]
      dsimp
      rw [mapRange_single, single_mul_single, mapRange_single, mapRange_single]
      simp only [mapRange_single, single_mul_single, ← op_mul, add_comm] }

-- @[simp] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10618): simp can prove this.
-- More specifically, the LHS simplifies to `Finsupp.single`, which implies there's some
-- defeq abuse going on.
theorem opRingEquiv_single [AddCommMonoid G] (r : k) (x : G) :
    AddMonoidAlgebra.opRingEquiv (op (single x r)) = single x (op r) := by simp

theorem opRingEquiv_symm_single [AddCommMonoid G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    AddMonoidAlgebra.opRingEquiv.symm (single x r) = op (single x r.unop) := by simp

end Opposite

end AddMonoidAlgebra
