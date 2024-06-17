/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.RingTheory.Kaehler

/-!
# The presheaf of differentials of a presheaf of modules

In order to do this, we first introduce the presheaf
of absolute differentials `absoluteDifferentials R` (i.e. the differentials over `ℤ`).

## Main definitions

- Given a presheaf of modules `M` over a presheaf of commutative rings, we define
the type `M.AbsoluteDerivation` of absolute derivations from `R` to `M`.

## TODO

- If `F : C ⥤ D` is a functor, and `f : S ⟶ F.op ⋙ R` a morphism of presheaves of rings,
construct the relative differentials of `f` as the quotient of `absoluteDifferentials R`
by the image of the canonical morphism from the pullback of `absoluteDifferentials S`:
this requires the construction of the pullback functor for presheaves of modules
(as a left adjoint to the functor constructed in the file
`Algebra.Category.ModuleCat.Presheaf.Pushforward`).
- Sheafify these constructions

-/

universe v u v₁ u₁

open CategoryTheory LinearMap Opposite

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

-- should be moved
instance : HasForget₂ CommRingCat AddCommGroupCat where
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R.α
      map := fun {R R'} φ => AddCommGroupCat.ofHom (AddMonoidHom.mk' φ.toFun (by simp)) }

variable {C : Type u₁} [Category.{v₁} C]

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- The type of absolute derivation from `R` to `M`, when `M` is a presheaf of modules
over the presheaf of commutative rings `R`. -/
@[ext]
structure AbsoluteDerivation where
  /-- the underlying additive map `R.obj X →+ M.obj X` of a derivation -/
  d {X : Cᵒᵖ} : R.obj X →+ M.obj X
  d_one (X : Cᵒᵖ) : d (X := X) 1 = 0 := by aesop_cat
  d_mul {X : Cᵒᵖ} (a b : R.obj X) : d (a * b) = a • d b + b • d a := by aesop_cat
  d_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    d (R.map f x) = M.map f (d x) := by aesop_cat

namespace AbsoluteDerivation

variable {M}

attribute [simp] d_one d_mul d_map

lemma congr_d {d d' : M.AbsoluteDerivation} (h : d = d') {X : Cᵒᵖ} (x : R.obj X) :
    d.d x = d'.d x := by subst h; rfl

variable (d : M.AbsoluteDerivation)

/-- Given an absolute derivation `d` of a presheaf of modules `M` over a
presheaf of commutative rings `R` on a category `C`, this is the
induced (absolute) derivation of the `R.obj X`-module `M.obj X` for all `X : Cᵒᵖ`. -/
@[simps]
def derivation (X : Cᵒᵖ) : Derivation ℤ (R.obj X) (M.obj X) where
  toFun x := d.d x
  map_add' := by simp
  map_smul' r x := by dsimp; rw [map_zsmul]
  map_one_eq_zero' := by simp
  leibniz' := by simp

variable {M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ M')

/-- The postcomposition of an absolute derivation of a presheaf of modules `M` by
a morphism `M ⟶ M'`. -/
def postcomp : AbsoluteDerivation M' where
  d {X} := (f.app X).toAddMonoidHom.comp d.d
  d_map {X Y} g x := by
    dsimp
    rw [d_map, naturality_apply]

@[simp]
lemma postcomp_d_apply {X : Cᵒᵖ} (x : R.obj X) :
    (d.postcomp f).d x = f.app _ (d.d x) := rfl

/-- The universal property that an absolute derivation `d : M.AbsoluteDerivation` must
satisfy so that the presheaf of modules `M` can be considered as the presheaf of
(absolute) differentials of a presheaf of commutative rings. -/
structure Universal where
  /-- An absolyte derivation of `M'` descends as a morphism `M ⟶ M'`. -/
  desc {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.AbsoluteDerivation) : M ⟶ M'
  fac {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.AbsoluteDerivation) : d.postcomp (desc d') = d' := by aesop_cat
  postcomp_injective {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (φ φ' : M ⟶ M') (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by aesop_cat

namespace Universal

variable {d}
variable (hR : d.Universal)

variable (M')

/-- If a derivation `d : M.AbsoluteDerivation` is universal,
this is the bijection `(M ⟶ M') ≃ M'.AbsoluteDerivation` for all `M'`. -/
def homEquiv : (M ⟶ M') ≃ M'.AbsoluteDerivation where
  toFun φ := d.postcomp φ
  invFun d' := hR.desc d'
  left_inv φ := hR.postcomp_injective _ _ (hR.fac (d.postcomp φ))
  right_inv d' := hR.fac d'

variable {M'}

@[simp]
lemma homEquiv_apply_d_apply (f : M ⟶ M') {X : Cᵒᵖ} (x : R.obj X) :
    (hR.homEquiv M' f).d x = f.app X (d.d x) := rfl

@[simp]
lemma homEquiv_symm_app_d (d' : M'.AbsoluteDerivation) {X : Cᵒᵖ} (x : R.obj X) :
    ((hR.homEquiv M').symm d').app X (d.d x) = d'.d x := by
  dsimp [homEquiv]
  conv_rhs => rw [← hR.fac d', postcomp_d_apply]

end Universal

end AbsoluteDerivation

variable (R)

/-- Auxiliary definition for `absoluteDifferentials`. -/
noncomputable def absoluteDifferentialsBundledCore :
    BundledCorePresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (Ω[(R.obj X)⁄ℤ])
  map {X Y} f := by
    letI := (R.map f).toAlgebra
    exact KaehlerDifferential.map ℤ ℤ (R.obj X) (R.obj Y)
  map_id X := by
    convert KaehlerDifferential.linearMap_ext _
    intro x
    erw [ModuleCat.restrictScalarsId'App_inv_apply]
    rw [KaehlerDifferential.map_D, R.map_id, Algebra.id.map_eq_id, RingHom.id_apply]
  map_comp {X Y Z} f g := by
    convert KaehlerDifferential.linearMap_ext _
    intro x
    letI := (R.map f).toAlgebra
    letI := (R.map g).toAlgebra
    dsimp
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    dsimp
    rw [KaehlerDifferential.map_D,
      ModuleCat.restrictScalarsComp'App_inv_apply]
    erw [KaehlerDifferential.map_D ℤ ℤ (R.obj X) (R.obj Y),
      KaehlerDifferential.map_D ℤ ℤ (R.obj Y) (R.obj Z), R.map_comp]
    rfl

/-- The presheaf of (absolute) differentials of a presheaf of commutative rings. -/
noncomputable def absoluteDifferentials :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  (absoluteDifferentialsBundledCore R).toPresheafOfModules

lemma absoluteDifferentials_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Ω[(R.obj X)⁄ℤ]) :
    (absoluteDifferentials R).map f x =
      letI := (R.map f).toAlgebra
      KaehlerDifferential.map ℤ ℤ (R.obj X) (R.obj Y) x := rfl

@[simp]
lemma absoluteDifferentials_map_apply_d {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    (absoluteDifferentials R).map f (KaehlerDifferential.D ℤ _ x) =
      KaehlerDifferential.D ℤ _ (R.map f x) := by
  letI := (R.map f).toAlgebra
  rw [absoluteDifferentials_map_apply]
  apply KaehlerDifferential.map_D

/-- The universal (absolute) derivation on the presheaf of modules `absoluteDifferentials R`. -/
noncomputable def absoluteDerivation : (absoluteDifferentials R).AbsoluteDerivation where
  d {X} := AddMonoidHom.mk' (fun x => KaehlerDifferential.D ℤ (R.obj X) x) (by simp)
  d_one := by dsimp; simp
  d_mul := by dsimp; simp
  d_map {X Y} f x := ((absoluteDifferentials_map_apply_d R f x)).symm

variable {R} in
@[simp]
lemma absoluteDerivation_d_apply {X : Cᵒᵖ} (x : R.obj X) :
    (absoluteDerivation R).d x = KaehlerDifferential.D ℤ (R.obj X) x := rfl

namespace absoluteDerivationUniversal

variable {R}
variable {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
  (d' : M'.AbsoluteDerivation)

/-- Auxiliary definition for `absoluteDerivationUniversal`. -/
noncomputable def desc : absoluteDifferentials R ⟶ M' :=
  Hom.mk'' (fun X => (d'.derivation X).liftKaehlerDifferential) (fun X Y f => by
    apply KaehlerDifferential.linearMap_ext (R := ℤ) (S := R.obj X)
    intro x
    dsimp
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply, restrictionApp_apply,
      restrictionApp_apply]
    dsimp
    rw [absoluteDifferentials_map_apply_d]
    erw [Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    rw [d'.derivation_apply, d'.derivation_apply, d'.d_map])

@[simp]
lemma desc_app_apply_d {X : Cᵒᵖ} (x : R.obj X) :
    (desc d').app X (KaehlerDifferential.D ℤ (R.obj X) x) = d'.d x := by
  dsimp [desc]
  apply Derivation.liftKaehlerDifferential_comp_D

@[simp]
lemma fac : (absoluteDerivation R).postcomp (desc d') = d' := by
  ext X x
  dsimp
  rw [desc_app_apply_d]

@[ext]
lemma postcomp_injective {φ φ' : absoluteDifferentials R ⟶ M'}
    (h : (absoluteDerivation R).postcomp φ = (absoluteDerivation R).postcomp φ') :
    φ = φ' := by
  ext1 X
  apply KaehlerDifferential.linearMap_ext ℤ (R.obj X)
  exact AbsoluteDerivation.congr_d h

end absoluteDerivationUniversal

open absoluteDerivationUniversal in
/-- The (absolute) derivation on the presheaf of modules `absoluteDifferentials R` is universal. -/
noncomputable def absoluteDerivationUniversal : (absoluteDerivation R).Universal where
  desc d' := desc d'

variable {R}
variable (M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- The bijection `(absoluteDifferentials R ⟶ M') ≃ M'.AbsoluteDerivation` for any presheaf
of modules `M` which is given by the universal property of `absoluteDifferentials R`. -/
noncomputable abbrev absoluteDerivationHomEquiv :
    (absoluteDifferentials R ⟶ M') ≃ M'.AbsoluteDerivation :=
  (absoluteDerivationUniversal R).homEquiv M'

@[simp]
lemma absoluteDerivationHomEquiv_symm_app_d
    (d' : M'.AbsoluteDerivation) {X : Cᵒᵖ} (x : R.obj X) :
    ((absoluteDerivationHomEquiv M').symm d').app X (KaehlerDifferential.D ℤ (R.obj X) x) =
      d'.d x :=
  (absoluteDerivationUniversal R).homEquiv_symm_app_d d' x

end PresheafOfModules
