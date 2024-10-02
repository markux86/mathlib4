/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Generator

/-! Generators for the category of presheaves of modules

In this file, given a presheaf of rings `R` on a category `C`,
we construct a set `FreeYoneda R` of presheaf of modules that
is separating and detecting: this set consists of presheaf of
modules of form `(free R).obj (yoneda.obj X)` for `X : C`,
i.e. free presheaves of modules generated by the yoneda
presheaf represented by some `X : C` (the functor
represented by such a presheaf of modules is the evaluation
functor `M ↦ M.obj (op X)`, see `freeYonedaEquiv`).

We deducde that if `C : Type u` is a small category,
and `R : Cᵒᵖ ⥤ RingCat.{u}`, then `PresheafOfModules.{u} R`
is a well powered category.

-/

universe u v w

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}
  {C₀ : Type u} [SmallCategory C₀] {R₀ : C₀ᵒᵖ ⥤ RingCat.{u}}

/-- When `R : Cᵒᵖ ⥤ RingCat`, `M : PresheafOfModules R`, and `X : C`, this is the
bijection `((free R).obj (yoneda.obj X) ⟶ M) ≃ M.obj (Opposite.op X)`. -/
noncomputable def freeYonedaEquiv (M : PresheafOfModules.{v} R) (X : C) :
    ((free R).obj (yoneda.obj X) ⟶ M) ≃ M.obj (Opposite.op X) :=
  freeHomEquiv.trans yonedaEquiv

variable (R) in
/-- The set of `PresheafOfModules.{v} R` consisting of objects of the
form `(free R).obj (yoneda.obj X)` for some `X`.  -/
inductive FreeYoneda : Set (PresheafOfModules.{v} R)
  | free_yoneda_mem (X : C) : FreeYoneda ((free R).obj (yoneda.obj X))

namespace FreeYoneda

/-- Constructor for the subtype associated to the set `FreeYoneda R`. -/
@[simps]
noncomputable def mk (X : C) : FreeYoneda R := ⟨(free R).obj (yoneda.obj X), ⟨X⟩⟩

lemma mk_surjective : Function.Surjective (mk (R := R)) := by
  rintro ⟨_, ⟨X⟩⟩
  exact ⟨X, rfl⟩

instance : Small.{u} (FreeYoneda R) :=
  small_of_surjective (mk_surjective (R := R))

variable (R)

lemma isSeparating : IsSeparating (FreeYoneda R) := by
  intro M N f₁ f₂ h
  ext ⟨X⟩ m
  obtain ⟨g, rfl⟩ := (freeYonedaEquiv M X).surjective m
  exact congr_arg (freeYonedaEquiv _ _) (h _ ⟨X⟩ g)

lemma isDetecting : IsDetecting (FreeYoneda R) :=
  (isSeparating R).isDetecting

end FreeYoneda

instance wellPowered : WellPowered (PresheafOfModules.{u} R₀) :=
  wellPowered_of_isDetecting (FreeYoneda.isDetecting R₀)

end PresheafOfModules
