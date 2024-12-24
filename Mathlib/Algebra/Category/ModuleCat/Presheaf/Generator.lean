/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Generator

/-!
# Generators for the category of presheaves of modules

In this file, given a presheaf of rings `R` on a category `C`,
we study the set `freeYoneda R` of presheaves of modules
of form `(free R).obj (yoneda.obj X)` for `X : C`, i.e.
free presheaves of modules generated by the Yoneda
presheaf represented by some `X : C` (the functor
represented by such a presheaf of modules is the evaluation
functor `M ↦ M.obj (op X)`, see `freeYonedaEquiv`).

Lemmas `PresheafOfModules.freeYoneda.isSeparating` and
`PresheafOfModules.freeYoneda.isDetecting` assert that this
set `freeYoneda R` is separating and detecting.
We deduce that if `C : Type u` is a small category,
and `R : Cᵒᵖ ⥤ RingCat.{u}`, then `PresheafOfModules.{u} R`
is a well-powered category.

Finally, given `M : PresheafOfModules.{u} R`, we consider
the canonical epimorphism of presheaves of modules
`M.fromFreeYonedaCoproduct : M.freeYonedaCoproduct ⟶ M`
where `M.freeYonedaCoproduct` is a coproduct indexed
by elements of `M`, i.e. pairs `⟨X : Cᵒᵖ, a : M.obj X⟩`,
of the objects `(free R).obj (yoneda.obj X.unop)`.
This is used in the definition
`PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork`
in order to obtain that any presheaf of modules is a cokernel
of a morphism between coproducts of objects in `freeYoneda R`.

-/

universe v v₁ u u₁

open CategoryTheory Limits

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

/-- When `R : Cᵒᵖ ⥤ RingCat`, `M : PresheafOfModules R`, and `X : C`, this is the
bijection `((free R).obj (yoneda.obj X) ⟶ M) ≃ M.obj (Opposite.op X)`. -/
noncomputable def freeYonedaEquiv {M : PresheafOfModules.{v} R} {X : C} :
    ((free R).obj (yoneda.obj X) ⟶ M) ≃ M.obj (Opposite.op X) :=
  freeHomEquiv.trans yonedaEquiv

lemma freeYonedaEquiv_symm_app (M : PresheafOfModules.{v} R) (X : C)
    (x : M.obj (Opposite.op X)) :
    (freeYonedaEquiv.symm x).app (Opposite.op X) (ModuleCat.freeMk (𝟙 _)) = x := by
  dsimp [freeYonedaEquiv, freeHomEquiv, yonedaEquiv]
  rw [ModuleCat.freeDesc_apply, op_id, M.presheaf.map_id]
  rfl

lemma freeYonedaEquiv_comp {M N : PresheafOfModules.{v} R} {X : C}
    (m : ((free R).obj (yoneda.obj X) ⟶ M)) (φ : M ⟶ N) :
    freeYonedaEquiv (m ≫ φ) = φ.app _ (freeYonedaEquiv m) := rfl

variable (R) in
/-- The set of `PresheafOfModules.{v} R` consisting of objects of the
form `(free R).obj (yoneda.obj X)` for some `X`.  -/
def freeYoneda : Set (PresheafOfModules.{v} R) := Set.range (yoneda ⋙ free R).obj

namespace freeYoneda

instance : Small.{u} (freeYoneda R) := by
  let π : C → freeYoneda R := fun X ↦ ⟨_, ⟨X, rfl⟩⟩
  have hπ : Function.Surjective π := by rintro ⟨_, ⟨X, rfl⟩⟩; exact ⟨X, rfl⟩
  exact small_of_surjective hπ

variable (R)

lemma isSeparating : IsSeparating (freeYoneda R) := by
  intro M N f₁ f₂ h
  ext ⟨X⟩ m
  obtain ⟨g, rfl⟩ := freeYonedaEquiv.surjective m
  exact congr_arg freeYonedaEquiv (h _ ⟨X, rfl⟩ g)

lemma isDetecting : IsDetecting (freeYoneda R) :=
  (isSeparating R).isDetecting

end freeYoneda

instance wellPowered {C₀ : Type u} [SmallCategory C₀] (R₀ : C₀ᵒᵖ ⥤ RingCat.{u}) :
    WellPowered.{u} (PresheafOfModules.{u} R₀) :=
  wellPowered_of_isDetecting (freeYoneda.isDetecting R₀)

/-- The type of elements of a presheaf of modules. A term of this type is a pair
`⟨X, a⟩` with `X : Cᵒᵖ` and `a : M.obj X`. -/
abbrev Elements {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  (M : PresheafOfModules.{v} R) := ((toPresheaf R).obj M ⋙ forget Ab).Elements

/-- Given a presheaf of modules `M`, this is a constructor for the type `M.Elements`. -/
abbrev elementsMk {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) (x : M.obj X) : M.Elements :=
  Functor.elementsMk _ X x

namespace Elements

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R}

/-- Given an element `m : M.Elements` of a presheaf of modules `M`, this is the
free presheaf of modules on the Yoneda presheaf of types corresponding to the
underlying object of `m`. -/
noncomputable abbrev freeYoneda (m : M.Elements) :
    PresheafOfModules.{v} R := (free R).obj (yoneda.obj m.1.unop)

/-- Given an element `m : M.Elements` of a presheaf of modules `M`, this is
the canonical morphism `m.freeYoneda ⟶ M`. -/
noncomputable abbrev fromFreeYoneda (m : M.Elements) :
    m.freeYoneda ⟶ M :=
  freeYonedaEquiv.symm m.2

lemma fromFreeYoneda_app_apply (m : M.Elements) :
    m.fromFreeYoneda.app m.1 (ModuleCat.freeMk (𝟙 _)) = m.2 := by
  apply freeYonedaEquiv_symm_app

end Elements

section

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

/-- Given a presheaf of modules `M`, this is the coproduct of
all free Yoneda presheaves `m.freeYoneda` for all `m : M.Elements`. -/
noncomputable abbrev freeYonedaCoproduct : PresheafOfModules.{u} R :=
  ∐ (Elements.freeYoneda (M := M))

/-- Given an element `m : M.Elements` of a presheaf of modules `M`, this is the
canonical inclusion `m.freeYoneda ⟶ M.freeYonedaCoproduct`. -/
noncomputable abbrev ιFreeYonedaCoproduct (m : M.Elements) :
    m.freeYoneda ⟶ M.freeYonedaCoproduct :=
  Sigma.ι _ m

/-- Given a presheaf of modules `M`, this is the
canonical morphism `M.freeYonedaCoproduct ⟶ M`. -/
noncomputable def fromFreeYonedaCoproduct :
    M.freeYonedaCoproduct ⟶ M :=
  Sigma.desc Elements.fromFreeYoneda

/-- Given an element `m` of a presheaf of modules `M`, this is the associated
canonical section of the presheaf `M.freeYonedaCoproduct` over the object `m.1`. -/
noncomputable def freeYonedaCoproductMk (m : M.Elements) :
    M.freeYonedaCoproduct.obj m.1 :=
  (M.ιFreeYonedaCoproduct m).app _ (ModuleCat.freeMk (𝟙 _))

@[reassoc (attr := simp)]
lemma ι_fromFreeYonedaCoproduct (m : M.Elements) :
    M.ιFreeYonedaCoproduct m ≫ M.fromFreeYonedaCoproduct = m.fromFreeYoneda := by
  apply Sigma.ι_desc

lemma ι_fromFreeYonedaCoproduct_apply (m : M.Elements) (X : Cᵒᵖ) (x : m.freeYoneda.obj X) :
    M.fromFreeYonedaCoproduct.app X ((M.ιFreeYonedaCoproduct m).app X x) =
      m.fromFreeYoneda.app X x :=
  congr_fun ((evaluation R X ⋙ forget _).congr_map (M.ι_fromFreeYonedaCoproduct m)) x

@[simp]
lemma fromFreeYonedaCoproduct_app_mk (m : M.Elements) :
    M.fromFreeYonedaCoproduct.app _ (M.freeYonedaCoproductMk m) = m.2 := by
  dsimp [freeYonedaCoproductMk]
  erw [M.ι_fromFreeYonedaCoproduct_apply m]
  rw [m.fromFreeYoneda_app_apply]

instance : Epi M.fromFreeYonedaCoproduct :=
  epi_of_surjective (fun X m ↦ ⟨M.freeYonedaCoproductMk (M.elementsMk X m),
    M.fromFreeYonedaCoproduct_app_mk (M.elementsMk X m)⟩)

/-- Given a presheaf of modules `M`, this is a morphism between coproducts
of free presheaves of modules on Yoneda presheaves which gives a presentation
of the module `M`, see `isColimitFreeYonedaCoproductsCokernelCofork`. -/
noncomputable def toFreeYonedaCoproduct :
    (kernel M.fromFreeYonedaCoproduct).freeYonedaCoproduct ⟶ M.freeYonedaCoproduct :=
  (kernel M.fromFreeYonedaCoproduct).fromFreeYonedaCoproduct ≫ kernel.ι _

@[reassoc (attr := simp)]
lemma toFreeYonedaCoproduct_fromFreeYonedaCoproduct :
    M.toFreeYonedaCoproduct ≫ M.fromFreeYonedaCoproduct = 0 := by
  simp [toFreeYonedaCoproduct]

/-- (Colimit) cofork which gives a presentation of a presheaf of modules `M` using
coproducts of free presheaves of modules on Yoneda presheaves. -/
noncomputable abbrev freeYonedaCoproductsCokernelCofork :
    CokernelCofork M.toFreeYonedaCoproduct :=
  CokernelCofork.ofπ _ M.toFreeYonedaCoproduct_fromFreeYonedaCoproduct

/-- If `M` is a presheaf of modules, the cokernel cofork
`M.freeYonedaCoproductsCokernelCofork` is a colimit, which means that
`M` can be expressed as a cokernel of the morphism `M.toFreeYonedaCoproduct`
between coproducts of free presheaves of modules on Yoneda presheaves. -/
noncomputable def isColimitFreeYonedaCoproductsCokernelCofork :
    IsColimit M.freeYonedaCoproductsCokernelCofork := by
  let S := ShortComplex.mk _ _ M.toFreeYonedaCoproduct_fromFreeYonedaCoproduct
  let T := ShortComplex.mk _ _ (kernel.condition M.fromFreeYonedaCoproduct)
  let φ : S ⟶ T :=
    { τ₁ := fromFreeYonedaCoproduct _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (T.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel

end

end PresheafOfModules
