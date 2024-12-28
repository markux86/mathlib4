/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/


import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.End

/-!

# Distributive monoidal categories

## Main definitions

A monoidal category `C` with binary coproducts is left distributive if the left tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)` can be promoted to an isomorphism. We refer to
this isomorphism as the left distributivity isomorphism.

A monoidal category `C` with binary coproducts is right distributive if the right tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X` can be promoted to an isomorphism. We refer to
this isomorphism as the right distributivity isomorphism.

A distributive monoidal category is a monoidal category that is both left and right distributive.

## Main results

- A symmetric monoidal category is left distributive if and only if it is right distributive.

- A closed monoidal category is left distributive.

- For a category `C` the category of endofunctors `C ⥤ C` is left distributive (but almost
  never right distributive). The left distributivity is tentamount to the fact that the coproduct
  in the functor categories is computed pointwise.

## TODO

Show that a distributive monoidal category whose unit is weakly terminal is finitary distributive.

Provide more examples of the distributive monoidal structure on the following categories:

- The category of abelian groups with the monoidal structure given by the tensor product of
  abelian groups.
- The category of R-modules with the monoidal structure given by the tensor product of modules.
- The category of vector bundles over a topological space where the monoidal structure is given by
  the tensor product of vector bundles.
- The category of pointed types with the monoidal structure given by the smash product of
  pointed types and the coproduct given by the wedge sum.

## References

[Hans-Joachim Baues, Mamuka Jibladze, Andy Tonks, Cohomology of
monoids in monoidal categories, in: Operads: Proceedings of Renaissance
Conferences, Contemporary Mathematics 202, AMS (1997) 137-166][MR1268290]

-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Limits Iso

/-- A monoidal category with binary coproducts is left distributive
if the left tensor product functor preserves binary coproducts. -/
class IsMonoidalLeftDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorLeft (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X)

/-- A monoidal category with binary coproducts is right distributive
if the right tensor product functor preserves binary coproducts. -/
class IsMonoidalRightDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory.{v} C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorRight (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X)

/-- A monoidal category with binary coproducts is distributive
if it is both left and right distributive. -/
class IsMonoidalDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory.{v} C] [HasBinaryCoproducts C] extends
  IsMonoidalLeftDistrib C, IsMonoidalRightDistrib C

variable {C} [Category.{v} C] [MonoidalCategory.{v} C] [HasBinaryCoproducts C]

example [IsMonoidalDistrib C] : IsMonoidalLeftDistrib C := by infer_instance

section IsMonoidalLeftDistrib

instance IsMonoidalLeftDistrib.preserves_binary_coproducts_tensorLeft
    [IsMonoidalLeftDistrib C] {X : C} :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) :=
  IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLeft X

instance IsMonoidalLeftDistrib.preservesColimit_pair_tensorLeft
    [IsMonoidalLeftDistrib C] {X Y Z : C} :
    PreservesColimit (pair Y Z) (tensorLeft X) :=
  (IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLeft X).preservesColimit

/-- The canonical left distributivity isomorphism -/
def leftDistrib [IsMonoidalLeftDistrib C] (X Y Z : C) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) :=
  PreservesColimitPair.iso (tensorLeft X) Y Z

/-- Notation for the forward direction morphism of the canonical left distributivity isomorphism -/
scoped notation "∂L" => leftDistrib

instance IsMonoidalLeftDistrib.isIso_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    IsIso (∂L X Y Z).hom :=
  isIso_hom <| leftDistrib X Y Z

instance IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorLeft X) Y Z)] : IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X := by
    refine {
      preservesColimit := by
        intro K
        have : PreservesColimit
          (pair (K.obj { as := WalkingPair.left }) (K.obj { as := WalkingPair.right }))
          (tensorLeft X) := by
            apply PreservesColimitPair.of_iso_coprod_comparison (tensorLeft X) _ _
        apply preservesColimit_of_iso_diagram (tensorLeft X) (diagramIsoPair K).symm
    }

variable [IsMonoidalLeftDistrib C]

/-- The forward direction of the left distributivity isomorphism is the cogap morphism
`coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)`. -/
@[simp]
lemma leftDistrib_hom {X Y Z : C} :
  (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) := by rfl

lemma coprod_inl_leftDistrib {X Y Z : C} :
    coprod.inl ≫ (∂L X Y Z).hom = (X ◁ coprod.inl) := by
  rw [leftDistrib_hom, coprod.inl_desc]

lemma coprod_inr_leftDistrib {X Y Z : C} :
  coprod.inr ≫ (∂L X Y Z).hom = (X ◁ coprod.inr) :=
by
  rw [leftDistrib_hom, coprod.inr_desc]

/-- The composite of `(X ◁ coprod.inl) : X ⊗ Y ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the left coprojection `coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
lemma whisker_inl_inv_leftDistrib {X Y Z : C} :
    (X ◁ coprod.inl) ≫ (∂L X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inl_leftDistrib]

/-- The composite of `(X ◁ coprod.inr) : X ⊗ Z ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the right coprojection `coprod.inr : X ⊗ Z ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
lemma whisker_inr_inv_leftDistrib {X Y Z : C} :
    (X ◁ coprod.inr) ≫ (∂L X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inr_leftDistrib]

end IsMonoidalLeftDistrib

section IsMonoidalRightDistrib

instance IsMonoidalRightDistrib.preserves_binary_coproducts_tensorRight
    [IsMonoidalRightDistrib C] {X : C} :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X) :=
  IsMonoidalRightDistrib.preservesBinaryCoproducts_tensorRight X

instance IsMonoidalRightDistrib.preservesColimit_pair_tensorRight
    [IsMonoidalRightDistrib C] {X Y Z : C} :
    PreservesColimit (pair Y Z) (tensorRight X) :=
  (IsMonoidalRightDistrib.preservesBinaryCoproducts_tensorRight X).preservesColimit

/-- The canonical right distributivity isomorphism -/
def rightDistrib [IsMonoidalRightDistrib C] (X Y Z : C) : (Y ⊗ X) ⨿ (Z ⊗ X) ≅ (Y ⨿ Z) ⊗ X :=
  PreservesColimitPair.iso (tensorRight X) Y Z

set_option quotPrecheck false in
/-- Notation for the forward direction morphism of the canonical right distributivity isomorphism -/
notation "∂R" => rightDistrib

instance IsMonoidalRightDistrib.isIso_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    IsIso (∂R X Y Z).hom :=
  isIso_hom <| rightDistrib X Y Z

instance IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorRight X) Y Z)] :
    IsMonoidalRightDistrib C where
  preservesBinaryCoproducts_tensorRight X := by
    refine {
      preservesColimit := by
        intro K
        have : PreservesColimit
          (pair (K.obj { as := WalkingPair.left }) (K.obj { as := WalkingPair.right }))
          (tensorRight X) := by
            apply PreservesColimitPair.of_iso_coprod_comparison (tensorRight X) _ _
        apply preservesColimit_of_iso_diagram (tensorRight X) (diagramIsoPair K).symm
    }

variable [IsMonoidalRightDistrib C]

/-- The forward direction of the right distributivity isomorphism is equal to the cogap morphism
`coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) : (Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X`. -/
@[simp]
lemma rightDistrib_hom {X Y Z : C} :
  (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) := by rfl

lemma coprod_inl_rightDistrib_hom {X Y Z : C} :
    coprod.inl ≫ (∂R X Y Z).hom = (coprod.inl ▷ X) := by
  rw [rightDistrib_hom, coprod.inl_desc]

lemma coprod_inr_rightDistrib_hom {X Y Z : C} :
    coprod.inr ≫ (∂R X Y Z).hom = (coprod.inr ▷ X) := by
  rw [rightDistrib_hom, coprod.inr_desc]

/-- The composite of `(coprod.inl ▷ X) : Y ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the left coprojection
`coprod.inl : Y ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
lemma whisker_inl_inv_rightDistrib {X Y Z : C} :
    (coprod.inl ▷ X) ≫ (∂R X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inl_rightDistrib_hom]

/-- The composite of `(coprod.inr ▷ X) : Z ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the right coprojection
`coprod.inr : Z ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
lemma whisker_inr_inv_rightDistrib {X Y Z : C} :
    (coprod.inr ▷ X) ≫ (∂R X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inr_rightDistrib_hom]

end IsMonoidalRightDistrib

/-- In a symmetric monoidal category, the left distributivity is equal to
the right distributivity up to braiding isomorphisms. -/
@[simp]
lemma SymmetricCategory.leftDistrib_braiding [SymmetricCategory C] {X Y Z : C} :
    (coprodComparison (tensorLeft X) Y Z) ≫ (β_ X (Y ⨿ Z)).hom =
    (coprod.map (β_ X Y).hom (β_ X Z).hom) ≫ (coprodComparison (tensorRight X) Y Z) := by
  simp [coprodComparison]


/-- In a symmetric monoidal category, the right distributivity is equal to
the left distributivity up to braiding isomorphisms. -/
@[simp]
lemma SymmetricCategory.rightDistrib_braiding [SymmetricCategory C] {X Y Z : C} :
    (coprodComparison (tensorRight X) Y Z) ≫ (β_ (Y ⨿ Z) X).hom =
    (coprod.map (β_ Y X).hom (β_ Z X).hom) ≫ (coprodComparison (tensorLeft X) Y Z) := by
  simp [coprodComparison]

/-- A left distributive symmetric monoidal category is right distributive. -/
instance SymmetricCategory.isMonoidalRightDistrib_of_isMonoidalLeftDistrib
    [SymmetricCategory C] [IsMonoidalLeftDistrib C] : IsMonoidalRightDistrib C where
  preservesBinaryCoproducts_tensorRight X :=
    preservesColimitsOfShape_of_natIso (SymmetricCategory.tensorLeftIsoTensorRight X)

/-- A left distributive symmetric monoidal category is distributive. -/
instance SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib
    [SymmetricCategory C] [IsMonoidalLeftDistrib C] : IsMonoidalDistrib C where

/-- The right distributivity isomorphism of the a left distributive symmetric monoidal category
is given by `(β_ (Y ⨿ Z) X).hom ≫ (∂L X Y Z).inv ≫ (coprod.map (β_ X Y).hom (β_ X Z).hom)`. -/
@[simp]
lemma SymmetricCategory.rightDistrib_of_leftDistrib
    [SymmetricCategory C] [IsMonoidalLeftDistrib C] {X Y Z : C} :
    ∂R X Y Z = (coprod.mapIso (β_ Y X) (β_ Z X)) ≪≫ (∂L X Y Z) ≪≫ (β_ X (Y ⨿ Z)) := by
  ext
  · simp
  · simp

/-- A closed monoidal category is left distributive. -/
instance MonoidalClosed.isMonoidalLeftDistrib [MonoidalClosed C] :
    IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X := {
    preservesColimit := ((ihom.adjunction X).leftAdjoint_preservesColimits).1.1
  }

/-- The inverse of distributivity isomorphism from the closed monoidal strurcture -/
@[simp]
lemma MonoidalClosed.leftDistrib_inv [MonoidalClosed C] {X Y Z : C} :
    (leftDistrib X Y Z).inv =
    MonoidalClosed.uncurry
      (coprod.desc (MonoidalClosed.curry coprod.inl) (MonoidalClosed.curry coprod.inr)) := by
  simp [← (MonoidalClosed.curry_eq_iff)]
  have : curry (∂L X Y Z).inv = coprod.desc
      (coprod.inl ≫ curry (∂L X Y Z).inv) (coprod.inr ≫ curry (∂L X Y Z).inv) := by
    aesop
  convert this
  · rw [← MonoidalClosed.curry_natural_left, whisker_inl_inv_leftDistrib]
  · rw [← MonoidalClosed.curry_natural_left, whisker_inr_inv_leftDistrib]

attribute [local instance] endofunctorMonoidalCategory

instance isIso_coprodComparison_tensorLeft_of_endofunctors {X Y Z : C ⥤ C} :
    IsIso (coprodComparison (tensorLeft X) Y Z) :=
  by
    refine ⟨?_, ?_, ?_⟩
    · exact {
    app (c : C) :=
    coprodObjIso Y Z (X.obj c) ≪≫ (coprodObjIso (X ⊗ Y) (X ⊗ Z) c).symm |>.hom
    }
    · ext c <;> simp [coprodComparison, coprodComparison, coprodObjIso]
    · ext c
      simp only [coprodComparison, coprodComparison, coprodObjIso, leftDistrib]
      aesop

/-- The monoidal structure on the category of endofunctors is left distributive. -/
instance isMonoidalLeftDistrib_of_endofunctors : IsMonoidalLeftDistrib (C ⥤ C) :=
  IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft

end CategoryTheory
