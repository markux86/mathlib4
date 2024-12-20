/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Left and right lifting properties

Given a morphism property `T`, we define the left and right lifting property with respect to `T`.

We show that the left lifting property is stable under retracts, cobase change, and composition,
with dual statements for the right lifting property.

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (T : MorphismProperty C)

namespace MorphismProperty

/-- The left lifting property (llp) with respect to a class of morphisms. -/
def llp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

/-- The right lifting property (rlp) with respect to a class of morphisms. -/
def rlp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f

lemma _root_.CategoryTheory.RetractArrow.leftLiftingProperty
    {X Y Z W Z' W' : C} {g : Z ⟶ W} {g' : Z' ⟶ W'}
    (h : RetractArrow g' g) (f : X ⟶ Y) [HasLiftingProperty g f] : HasLiftingProperty g' f where
  sq_hasLift := fun {u v} sq ↦ by
    have sq' : CommSq (h.r.left ≫ u) g f (h.r.right ≫ v) := by simp [sq.w]
    exact
      ⟨⟨{ l := h.i.right ≫ sq'.lift
          fac_left := by
            simp only [← h.i_w_assoc, sq'.fac_left, h.retract_left_assoc,
              Arrow.mk_left, Category.id_comp]
          fac_right := by simp}⟩⟩

lemma _root_.CategoryTheory.RetractArrow.rightLiftingProperty
    {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : RetractArrow f' f) (g : Z ⟶ W) [HasLiftingProperty g f] : HasLiftingProperty g f' where
  sq_hasLift := fun {u v} sq ↦ by
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← Category.assoc, ← sq.w, Category.assoc, RetractArrow.i_w, Category.assoc]⟩
    exact
      ⟨⟨{ l := sq'.lift ≫ h.r.left
          fac_left := by simp
          fac_right := by simp}⟩⟩

lemma _root_.CategoryTheory.IsPushout.leftLiftingProperty
    {X Y Z W Z' W' : C} {f : X ⟶ Y} {s : X ⟶ Z} {g : Z ⟶ W} {t : Y ⟶ W}
    (h : IsPushout s f g t) (g' : Z' ⟶ W') [HasLiftingProperty f g'] :
    HasLiftingProperty g g' where
  sq_hasLift := fun {u v} sq ↦ by
    have w : (s ≫ u) ≫ g' = f ≫ (t ≫ v) := by
      rw [← Category.assoc, ← h.w, Category.assoc, Category.assoc, sq.w]
    exact ⟨h.desc u (CommSq.mk w).lift (by rw [CommSq.fac_left]), h.inl_desc ..,
      h.hom_ext (by rw [h.inl_desc_assoc, sq.w]) (by rw [h.inr_desc_assoc, CommSq.fac_right])⟩

lemma _root_.CategoryTheory.IsPullback.rightLiftingProperty
    {X Y Z W X' Y' : C} {f : X ⟶ Y} {s : X ⟶ Z} {g : Z ⟶ W} {t : Y ⟶ W}
    (h : IsPullback s f g t) (f' : X' ⟶ Y') [HasLiftingProperty f' g] :
    HasLiftingProperty f' f where
  sq_hasLift := fun {u v} sq ↦ by
    have w : (u ≫ s) ≫ g = f' ≫ v ≫ t := by
      rw [Category.assoc, h.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
    exact ⟨h.lift (CommSq.mk w).lift v (by rw [CommSq.fac_right]),
      h.hom_ext (by rw [Category.assoc, h.lift_fst, CommSq.fac_left])
        (by rw [Category.assoc, h.lift_snd, sq.w]), h.lift_snd _ _ _⟩

lemma llp.IsStableUnderRetracts : T.llp.IsStableUnderRetracts where
  of_retract h hg _ _ f hf :=
    letI := hg _ hf
    RetractArrow.leftLiftingProperty h f

lemma rlp.IsStableUnderRetracts : T.rlp.IsStableUnderRetracts where
  of_retract h hf _ _ g hg :=
    letI := hf _ hg
    RetractArrow.rightLiftingProperty h g

instance llp.IsStableUnderCobaseChange : T.llp.IsStableUnderCobaseChange where
  of_isPushout h hf _ _ g' hg' :=
    letI := hf _ hg'
    IsPushout.leftLiftingProperty h g'

open IsPullback in
instance rlp.IsStableUnderBaseChange : T.rlp.IsStableUnderBaseChange where
  of_isPullback h hf _ _ f' hf' :=
    letI := hf _ hf'
    IsPullback.rightLiftingProperty h f'

instance llp.IsMultiplicative : T.llp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

instance rlp.IsMultiplicative : T.rlp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

end MorphismProperty

end CategoryTheory
