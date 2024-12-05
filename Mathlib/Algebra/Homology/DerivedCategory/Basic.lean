/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Localization

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. It is equipped with a triangulated structure.

The derived category is defined here as the localization of cochain complexes
indexed by `ℤ` with respect to quasi-isomorphisms: it is a type synonym of
`HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`. Then, we have a
localization functor `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`.
It was already shown in the file `Algebra.Homology.Localization` that the induced
functor `DerivedCategory.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`
is a localization functor with respect to the class of morphisms
`HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`. In the lemma
`HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W` we obtain that this class of morphisms
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes. Then, the triangulated
structure on `DerivedCategory C` is deduced from the triangulated structure
on the homotopy category (see file `Algebra.Homology.HomotopyCategory.Triangulated`)
using the localization theorem for triangulated categories which was obtained
in the file `CategoryTheory.Localization.Triangulated`.

## Implementation notes

If `C : Type u` and `Category.{v} C`, the constructed localized category of cochain
complexes with respect to quasi-isomorphisms has morphisms in `Type (max u v)`.
However, in certain circumstances, it shall be possible to prove that they are `v`-small
(when `C` is a Grothendieck abelian category (e.g. the category of modules over a ring),
it should be so by a theorem of Hovey.).

Then, when working with derived categories in mathlib, the user should add the variable
`[HasDerivedCategory.{w} C]` which is the assumption that there is a chosen derived
category with morphisms in `Type w`. When derived categories are used in order to
prove statements which do not involve derived categories, the `HasDerivedCategory.{max u v}`
instance should be obtained at the beginning of the proof, using the term
`HasDerivedCategory.standard C`.

## TODO (@joelriou)

- construct the distinguished triangle associated to a short exact sequence
of cochain complexes (done), and compare the associated connecting homomorphism
with the one defined in `Algebra.Homology.HomologySequence`.
- refactor the definition of Ext groups using morphisms in the derived category
(which may be shrunk to the universe `v` at least when `C` has enough projectives
or enough injectives).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]

-/

universe w v u

open CategoryTheory Category Limits Pretriangulated ZeroObject

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

/-- The triangulated subcategory of `HomotopyCategory C (ComplexShape.up ℤ)` consisting
of acyclic complexes. -/
def subcategoryAcyclic : Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (homologyFunctor C (ComplexShape.up ℤ) 0).homologicalKernel

instance : ClosedUnderIsomorphisms (subcategoryAcyclic C).P := by
  dsimp [subcategoryAcyclic]
  infer_instance

variable {C}

lemma mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (subcategoryAcyclic C).P X ↔ ∀ (n : ℤ), IsZero ((homologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X

lemma quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C ℤ) :
    (subcategoryAcyclic C).P ((quotient _ _).obj K) ↔ ∀ (n : ℤ), K.ExactAt n := by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app K).isZero_iff

lemma quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C ℤ) :
    (subcategoryAcyclic C).P ((quotient _ _).obj K) ↔ K.Acyclic := by
  apply quotient_obj_mem_subcategoryAcyclic_iff_exactAt

variable (C)

lemma quasiIso_eq_subcategoryAcyclic_W :
    quasiIso C (ComplexShape.up ℤ) = (subcategoryAcyclic C).W := by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up ℤ) 0).mem_homologicalKernel_W_iff f).symm

instance : (quasiIso C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

lemma quasiIso_respectsIso : (quasiIso C (ComplexShape.up ℤ)).RespectsIso := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  apply Triangulated.Subcategory.respectsIso_W

end HomotopyCategory

/-- The assumption that a localized category for
`(HomologicalComplex.quasiIso C (ComplexShape.up ℤ))` has been chosen, and that the morphisms
in this chosen category are in `Type w`. -/
abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

/-- The derived category obtained using the constructed localized category of cochain complexes
with respect to quasi-isomorphisms. This should be used only while proving statements
which do not involve the derived category. -/
def HasDerivedCategory.standard : HasDerivedCategory.{max u v} C :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategory.{w} C]

/-- The derived category of an abelian category. -/
def DerivedCategory : Type (max u v) := HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)

namespace DerivedCategory

instance : Category.{w} (DerivedCategory C) := by
  dsimp [DerivedCategory]
  infer_instance

variable {C}

/-- The localization functor `CochainComplex C ℤ ⥤ DerivedCategory C`. -/
def Q : CochainComplex C ℤ ⥤ DerivedCategory C := HomologicalComplexUpToQuasiIso.Q

instance : (Q (C := C)).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [Q, DerivedCategory]
  infer_instance

instance {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (Q.map f) :=
  Localization.inverts Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _
    (inferInstanceAs (QuasiIso f))

/-- The localization functor `HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`. -/
def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  HomologicalComplexUpToQuasiIso.Qh

variable (C)

/-- The natural isomorphism `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q`. -/
def quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q :=
  HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up ℤ)

instance : Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance

instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).W := by
  rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

noncomputable instance : HasZeroObject (DerivedCategory C) :=
  Q.hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Q (C := C)).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ

instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ

instance shiftFunctor_additive (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).W]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

noncomputable instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance (n : ℤ) :
  Localization.Lifting Qh (HomotopyCategory.subcategoryAcyclic C).W
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n) := ⟨(Qh.commShiftIso n).symm⟩

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).W

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful

instance : (Q : _ ⥤ DerivedCategory C).mapArrow.EssSurj where
  mem_essImage φ := by
    obtain ⟨⟨K⟩, ⟨L⟩, f, ⟨e⟩⟩ :
        ∃ (K L : HomotopyCategory C (ComplexShape.up ℤ)) (f : K ⟶ L),
          Nonempty (Arrow.mk (Qh.map f) ≅ φ) := ⟨_, _, _, ⟨Qh.mapArrow.objObjPreimageIso φ⟩⟩
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    exact ⟨Arrow.mk f, ⟨e⟩⟩

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (Qh : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

instance : (Q : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

variable {C} in
lemma mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

lemma induction_Q_obj (P : DerivedCategory C → Prop)
    (hP₁ : ∀ (X : CochainComplex C ℤ), P (Q.obj X))
    (hP₂ : ∀ ⦃X Y : DerivedCategory C⦄ (_ : X ≅ Y), P X → P Y)
    (X : DerivedCategory C) : P X :=
  hP₂ (Q.objObjPreimageIso X) (hP₁ _)

/-- The single functors `C ⥤ DerivedCategory C` for all `n : ℤ` along with
their compatibilities with shifts. -/
noncomputable def singleFunctors : SingleFunctors C (DerivedCategory C) ℤ :=
  (HomotopyCategory.singleFunctors C).postcomp Qh

/-- The shift functor `C ⥤ DerivedCategory C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`. -/
noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

/-- The isomorphism
`DerivedCategory.singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh` given
by the definition of `DerivedCategory.singleFunctors`. -/
noncomputable def singleFunctorsPostcompQhIso :
    singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh :=
  Iso.refl _

/-- The isomorphism
`DerivedCategory.singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q`. -/
noncomputable def singleFunctorsPostcompQIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q :=
  (SingleFunctors.postcompFunctor C ℤ (Qh : _ ⥤ DerivedCategory C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

lemma singleFunctorsPostcompQIso_hom_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id, SingleFunctors.id_hom, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  rfl

lemma singleFunctorsPostcompQIso_inv_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  erw [CategoryTheory.Functor.map_id]
  rw [SingleFunctors.id_hom, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  rfl

noncomputable def singleFunctorIsoCompQ (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q := Iso.refl _

lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

/- to be moved to TStructure.Basic
noncomputable def DerivedCategory.singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  isoWhiskerRight ((SingleFunctors.evaluation _ _ n).mapIso
    (singleFunctorsPostCompQIso C)) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
      HomologicalComplex.homologyFunctorSingleIso _ _ _
-/

/-
variable {C}

lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · intro hf
    exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ hf

lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

lemma isIso_Q_map_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔
      ∀ (n : ℤ), IsIso ((HomologicalComplex.homologyFunctor C _ n).map φ) := by
  simp only [isIso_Q_map_iff_quasiIso, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap]
  rfl

lemma isIso_Q_map_iff' {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ HomologicalComplex.quasiIso _ _ φ := by
  rw [isIso_Q_map_iff_quasiIso]
  rfl

instance {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ] : IsIso (Q.map φ) := by
  simpa only [isIso_Q_map_iff_quasiIso]

lemma isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  · intro hf n
    infer_instance
  · intro hf
    let g := (Functor.mapArrow Qh).objPreimage (Arrow.mk f)
    refine' ((MorphismProperty.RespectsIso.isomorphisms (DerivedCategory C)).arrow_iso_iff
      ((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f))).1 _
    change IsIso (Qh.map g.hom)
    rw [isIso_Qh_map_iff, HomotopyCategory.mem_quasiIso_iff]
    intro n
    have e : Arrow.mk ((homologyFunctor C n).map f) ≅
        Arrow.mk ((HomotopyCategory.homologyFunctor _ _ n).map g.hom) :=
      ((homologyFunctor C n).mapArrow.mapIso
        (((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f)).symm)) ≪≫
        ((Functor.mapArrowFunctor _ _).mapIso (homologyFunctorFactorsh C n)).app (Arrow.mk g.hom)
    exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_iso_iff e).1 (hf n)

lemma isZero_iff (K : DerivedCategory C) :
    IsZero K ↔ ∀ (n : ℤ), IsZero ((homologyFunctor C n).obj K) := by
  constructor
  · intro hK n
    rw [IsZero.iff_id_eq_zero, ← ((homologyFunctor C n).map_id K),
      (IsZero.iff_id_eq_zero K).1 hK, Functor.map_zero]
  · intro hK
    have : IsIso (0 : K ⟶ 0) := by
      rw [isIso_iff]
      intro n
      refine' ⟨0, _, _⟩
      · apply (hK n).eq_of_src
      · rw [zero_comp, ← (homologyFunctor C n).map_id, id_zero,
          Functor.map_zero]
    exact IsZero.of_iso (isZero_zero _) (asIso (0 : K ⟶ 0))

-/

end DerivedCategory
