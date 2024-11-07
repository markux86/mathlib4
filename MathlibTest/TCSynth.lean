/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Yuyang Zhao
-/
import Mathlib

/-!
# Test against slow typeclass synthesis

This file tests against regression in typeclass synthesis speed.
The tests below became fast by the fix in
https://github.com/leanprover/lean4/pull/4085
-/

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12226

open Complex Filter Bornology

/--
error: failed to synthesize
  AddMonoidHomClass (AddGroupSeminorm ℂ) ℂ ℝ
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 3000 in
#synth AddMonoidHomClass (AddGroupSeminorm ℂ) ℂ ℝ

-- This then results in a near failure (or failure on nightly-testing) of the simpNF linter on
-- `Complex.comap_exp_cobounded` and `Complex.map_exp_comap_re_atTop`:

set_option synthInstance.maxHeartbeats 3000 in
example : comap exp (cobounded ℂ) = comap re atTop := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12227

/-- info: NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring -/
#guard_msgs in
variable {A : Type} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
  [CStarRing A] [StarModule ℂ A] (x : A) in
#synth NonUnitalNonAssocSemiring (elementalStarAlgebra ℂ x)

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12229

open Real in
set_option synthInstance.maxHeartbeats 10000 in
example : Circle.exp (2 * π) = 1 := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12230

open Complex in
set_option synthInstance.maxHeartbeats 3200 in
example (x : ℝ) : abs (cos x + sin x * I) = 1 := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12231

variable {α m n : Type*}

open Matrix in
set_option synthInstance.maxHeartbeats 2000 in
example [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12232
-- reduced from 9000 to 1000 after `@[simp low] map_zero` in #16679 (only 10 needed)

open Equiv in
set_option synthInstance.maxHeartbeats 1000 in
example {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) 0 = p := by simp

end

section

open scoped IntermediateField in
set_option synthInstance.maxHeartbeats 3000 in
example {K L B : Type u} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B] (α : L) :
    AddHomClass (K⟮α⟯ →ₐ[K] B) K⟮α⟯ B :=
  inferInstance

end

section

open TensorProduct in
set_option synthInstance.maxHeartbeats 6000 in
example {R A S : Type*} [CommRing R] [CommRing A] [Algebra A R] [CommRing S] [Algebra A S]
    {S₀ : Subalgebra A S} {T₀ : Subalgebra A R} :
    AddHomClass (T₀ ⊗[A] S₀ →ₐ[A] R ⊗[A] S) (T₀ ⊗[A] S₀) (R ⊗[A] S) :=
  inferInstance

end
