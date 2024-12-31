/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The pullback of a shift by a monoid morphism

Given a shift by a monoid `B` on a category `C` and a monoid morphism  `φ : A →+ B`,
we define a shift by `A` on a category `PullbackShift C φ` which is a type synonym for `C`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `B`, and if `F`
has a `CommShift` structure by `B`, we define a pulled back `CommShift` structure by `A`
on `F`.
We also prove that, if an adjunction `F ⊣ G` is compatible with `CommShift` structures
on `F` and `G`, then it is also compatible with the pulled back `CommShift` structures.
-/

namespace CategoryTheory

open Limits Category

variable (C : Type*) [Category C] {A B : Type*} [AddMonoid A] [AddMonoid B]
  (φ : A →+ B) [HasShift C B]

/-- The category `PullbackShift C φ` is equipped with a shift such that for all `a`,
the shift functor by `a` is `shiftFunctor C (φ a)`. -/
@[nolint unusedArguments]
def PullbackShift (_ : A →+ B) [HasShift C B] := C

instance : Category (PullbackShift C φ) := by
  dsimp only [PullbackShift]
  infer_instance

attribute [local instance] endofunctorMonoidalCategory

/-- The shift on `PullbackShift C φ` is obtained by precomposing the shift on `C` with
the monoidal functor `Discrete.addMonoidalFunctor φ : Discrete A ⥤ Discrete B`. -/
noncomputable instance : HasShift (PullbackShift C φ) A where
  shift := Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B

instance [HasZeroObject C] : HasZeroObject (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] : Preadditive (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] (a : A) [(shiftFunctor C (φ a)).Additive] :
    (shiftFunctor (PullbackShift C φ) a).Additive := by
  change (shiftFunctor C (φ a)).Additive
  infer_instance

/-- When `b = φ a`, this is the canonical
isomorphism `shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b`. -/
noncomputable def pullbackShiftIso (a : A) (b : B) (h : b = φ a) :
    shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b := eqToIso (by subst h; rfl)

variable {C}
variable (X : PullbackShift C φ) (a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B)
  (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a₂) (h₃ : b₃ = φ a₃)

lemma pullbackShiftFunctorZero_inv_app :
    (shiftFunctorZero _ A).inv.app X =
      (shiftFunctorZero C B).inv.app X ≫ (pullbackShiftIso C φ 0 0 (by simp)).inv.app X := by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

lemma pullbackShiftFunctorZero_hom_app :
    (shiftFunctorZero _ A).hom.app X =
      (pullbackShiftIso C φ 0 0 (by simp)).hom.app X ≫ (shiftFunctorZero C B).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

lemma pullbackShiftFunctorZero'_inv_app :
    (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero' C (φ 0) (by rw [map_zero])).inv.app X ≫
      (pullbackShiftIso C φ 0 (φ 0) rfl).inv.app X := by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

lemma pullbackShiftFunctorZero'_hom_app :
    (shiftFunctorZero _ A).hom.app X = (pullbackShiftIso C φ 0 (φ 0) rfl).hom.app X ≫
      (shiftFunctorZero' C (φ 0) (by rw [map_zero])).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero'_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

lemma pullbackShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).hom.app X) ≫
        (pullbackShiftIso C φ a₂ b₂ h₂).hom.app _ ≫
        (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).inv.app X ≫
        (pullbackShiftIso C φ a₃ b₃ h₃).inv.app X := by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

lemma pullbackShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).hom.app X =
      (pullbackShiftIso C φ a₃ b₃ h₃).hom.app X ≫
      (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).hom.app X ≫
      (pullbackShiftIso C φ a₂ b₂ h₂).inv.app _ ≫
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).inv.app X) := by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃, assoc, assoc, assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rfl

namespace Functor

variable {D : Type*} [Category D] [HasShift D B] (F : C ⥤ D) [F.CommShift B]

/-- If `F : C ⥤ D` commutes with the shifts on `C` and `D`, then it also commutes with
their pullbacks by an additive map.
-/
noncomputable def commShiftPullback :
    F.CommShift A (C := PullbackShift C φ) (D := PullbackShift D φ) where
  iso a := isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) F ≪≫
    F.commShiftIso (φ a) ≪≫ isoWhiskerLeft _  (pullbackShiftIso D φ a (φ a) rfl).symm
  zero := by
    ext
    dsimp
    simp only [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero]), CommShift.isoZero'_hom_app,
      assoc, CommShift.isoZero_hom_app, pullbackShiftFunctorZero'_hom_app, map_comp,
      pullbackShiftFunctorZero'_inv_app]
    dsimp
    rfl
  add a b := by
    ext
    dsimp
    simp only [CommShift.isoAdd_hom_app, map_comp, assoc]
    dsimp
    rw [F.commShiftIso_add' (a := φ a) (b := φ b) (by rw [φ.map_add]),
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
      pullbackShiftFunctorAdd'_hom_app φ _ a b (a + b) rfl (φ a) (φ b) (φ (a + b)) rfl rfl rfl,
      pullbackShiftFunctorAdd'_inv_app φ _ a b (a + b) rfl (φ a) (φ b) (φ (a + b)) rfl rfl rfl]
    dsimp
    simp only [CommShift.isoAdd'_hom_app, assoc, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    erw [id_comp]
    slice_rhs 6 7 => erw [← (CommShift.iso (φ b)).hom.naturality]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ b (φ b) rfl).hom.naturality, map_comp]
    simp only [comp_obj, Functor.comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    slice_rhs 4 5 => rw [← map_comp]; erw [← map_comp]; rw [Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp, id_comp, assoc, assoc]; rfl

lemma commShiftPullback_iso_eq (a : A) (b : B) (h : b = φ a) :
    letI : F.CommShift (C := PullbackShift C φ) (D := PullbackShift D φ) A := F.commShiftPullback φ
    F.commShiftIso a (C := PullbackShift C φ) (D := PullbackShift D φ) =
      isoWhiskerRight (pullbackShiftIso C φ a b h) F ≪≫ (F.commShiftIso b) ≪≫
        isoWhiskerLeft F (pullbackShiftIso D φ a b h).symm := by
  obtain rfl : b = φ a := h
  rfl

end Functor

namespace Adjunction

variable {D : Type*} [Category D] [HasShift D B] {F : C ⥤ D} [F.CommShift B] {G : D ⥤ C}
  [G.CommShift B] (adj : F ⊣ G)

/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G`, then
it is also compatible with the pulled back `CommShift` structures by an additive map
`φ : B →+ A`.
-/
lemma commShiftPullback_of_commShift [adj.CommShift B] :
    letI := F.commShiftPullback φ
    letI := G.commShiftPullback φ
    adj.CommShift A (C := PullbackShift C φ) (D := PullbackShift D φ) := by
  letI := F.commShiftPullback φ
  letI := G.commShiftPullback φ
  refine Adjunction.CommShift.mk' _ _ (NatTrans.CommShift.mk (fun a ↦ ?_))
  ext X
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.commShiftIso_id_hom_app,
    whiskerRight_app, id_comp, whiskerLeft_app]
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftPullback_iso_eq _ _ _ _ rfl,
    Functor.commShiftPullback_iso_eq _ _ _ _ rfl, ← cancel_mono ((pullbackShiftIso C φ a _
    rfl).hom.app _), (pullbackShiftIso C φ a _ rfl).hom.naturality]
  simp only [Functor.comp_obj, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.map_comp, assoc,
    unit_naturality_assoc, Iso.inv_hom_id_app, comp_id, NatIso.cancel_natIso_hom_left]
  slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
  rw [id_comp]
  have := (CommShift.commShift_unit (adj := adj) (A := B)).comm' (φ a)
  apply_fun (fun h ↦ (h.app X)) at this
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.commShiftIso_id_hom_app,
    whiskerRight_app, id_comp, whiskerLeft_app, Functor.commShiftIso_comp_hom_app] at this
  exact this

end Adjunction

end CategoryTheory
