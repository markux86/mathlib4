/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Calle Sönne
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pasting lemma

This file proves the pasting lemma for pullbacks. That is, given the following diagram:
```
  X₁ - f₁ -> X₂ - f₂ -> X₃
  |          |          |
  i₁         i₂         i₃
  ∨          ∨          ∨
  Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
if the right square is a pullback, then the left square is a pullback iff the big square is a
pullback.

## Main results
* `bigSquareIsPullback` shows that the big square is a pullback if both the small squares are.
* `leftSquareIsPullback` shows that the left square is a pullback if the other two are.
* `pullbackRightPullbackFstIso` shows, using the `pullback` API, that
`W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`.

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section PasteLemma
section temp

/- Consider the following diagram

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃


-/

variable {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃} (t₂ : PullbackCone g₂ i₃)
variable (t₁ : PullbackCone g₁ t₂.fst)

local notation "X₂" => t₂.pt
local notation "i₂" => t₂.fst
local notation "f₂" => t₂.snd
local notation "X₁" => t₁.pt
local notation "i₁" => t₁.fst
local notation "f₁" => t₁.snd

abbrev PullbackCone.paste : PullbackCone (g₁ ≫ g₂) i₃ :=
  PullbackCone.mk i₁ (f₁ ≫ f₂) (by rw [reassoc_of% t₁.condition, Category.assoc, ← t₂.condition])

variable {t₂} {t₁}

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def bigSquareIsPullback' (H : IsLimit t₂) (H' : IsLimit t₁) : IsLimit (t₂.paste t₁) := by
  apply PullbackCone.isLimitAux'
  intro s
  -- obtain both limits
  obtain ⟨l₂, hl₂, hl₂'⟩ := PullbackCone.IsLimit.lift' H (s.fst ≫ g₁) s.snd
    (by rw [← s.condition, Category.assoc])
  obtain ⟨l₁, hl₁, hl₁'⟩ := PullbackCone.IsLimit.lift' H' s.fst l₂ hl₂.symm
  --
  refine ⟨l₁, hl₁, by simp [reassoc_of% hl₁', hl₂'], ?_⟩
  -- Uniqueness
  intro m hm₁ hm₂
  apply PullbackCone.IsLimit.hom_ext H' (by simpa [hl₁] using hm₁)
  apply PullbackCone.IsLimit.hom_ext H
  · dsimp at hm₁
    rw [Category.assoc, ← t₁.condition, reassoc_of% hm₁, hl₁', hl₂]
  · simpa [hl₁', hl₂'] using hm₂

def leftSquareIsPullback' (H : IsLimit t₂) (H' : IsLimit (t₂.paste t₁)) : IsLimit t₁ := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the induced morphism from the universal property of the big square
  obtain ⟨l, hl, hl'⟩ := PullbackCone.IsLimit.lift' H' s.fst (s.snd ≫ f₂)
    (by rw [Category.assoc, ← t₂.condition, reassoc_of% s.condition])
  refine ⟨l, hl, ?_, ?_⟩
  -- Check that ....
  · apply PullbackCone.IsLimit.hom_ext H
    · rw [← s.condition, ← hl, Category.assoc, ←t₁.condition, Category.assoc]
      rfl
    · simpa using hl'
  -- Uniqueness
  · intro m hm₁ hm₂
    apply PullbackCone.IsLimit.hom_ext H' (by simpa [hm₁] using hl.symm)
    dsimp at hl' ⊢
    rw [reassoc_of% hm₂, hl']

end temp

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
variable (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
variable (h₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = f₂ ≫ i₃)


/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def bigSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' : IsLimit (PullbackCone.mk _ _ h₁)) :
    IsLimit (PullbackCone.mk i₁ (f₁ ≫ f₂) (by rw [reassoc_of% h₁, Category.assoc, h₂])) :=
  bigSquareIsPullback' H H'
#align category_theory.limits.big_square_is_pullback CategoryTheory.Limits.bigSquareIsPullback

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pushout if both the small squares are.
-/
def bigSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₂))
    (H' : IsColimit (PushoutCocone.mk _ _ h₁)) :
    IsColimit
      (PushoutCocone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc])) := by
  fapply PushoutCocone.isColimitAux'
  intro s
  have : i₁ ≫ s.inl = f₁ ≫ f₂ ≫ s.inr := by rw [s.condition, Category.assoc]
  rcases PushoutCocone.IsColimit.desc' H' s.inl (f₂ ≫ s.inr) this with ⟨l₁, hl₁, hl₁'⟩
  rcases PushoutCocone.IsColimit.desc' H l₁ s.inr hl₁' with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use
    show (g₁ ≫ g₂) ≫ l₂ = s.inl by
      rw [← hl₁, ← hl₂, Category.assoc]
      rfl
  use hl₂'
  intro m hm₁ hm₂
  apply PushoutCocone.IsColimit.hom_ext H
  · apply PushoutCocone.IsColimit.hom_ext H'
    · erw [← Category.assoc, hm₁, hl₂, hl₁]
    · erw [← Category.assoc, h₂, Category.assoc, hm₂, ← hl₂', ← Category.assoc, ← Category.assoc, ←
        h₂]
      rfl
  · erw [hm₂, hl₂']
#align category_theory.limits.big_square_is_pushout CategoryTheory.Limits.bigSquareIsPushout

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the left square is a pullback if the right square and the big square are.
-/
def leftSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' :
      IsLimit
        (PullbackCone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]))) :
    IsLimit (PullbackCone.mk _ _ h₁) :=
  leftSquareIsPullback' H H'
#align category_theory.limits.left_square_is_pullback CategoryTheory.Limits.leftSquareIsPullback

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def rightSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₁))
    (H' :
      IsColimit
        (PushoutCocone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]))) :
    IsColimit (PushoutCocone.mk _ _ h₂) := by
  fapply PushoutCocone.isColimitAux'
  intro s
  have : i₁ ≫ g₁ ≫ s.inl = (f₁ ≫ f₂) ≫ s.inr := by
    rw [Category.assoc, ← s.condition, ← Category.assoc, ← Category.assoc, h₁]
  rcases PushoutCocone.IsColimit.desc' H' (g₁ ≫ s.inl) s.inr this with ⟨l₁, hl₁, hl₁'⟩
  dsimp at *
  use l₁
  refine ⟨?_, ?_, ?_⟩
  · apply PushoutCocone.IsColimit.hom_ext H
    · erw [← Category.assoc, hl₁]
      rfl
    · erw [← Category.assoc, h₂, Category.assoc, hl₁', s.condition]
  · exact hl₁'
  · intro m hm₁ hm₂
    apply PushoutCocone.IsColimit.hom_ext H'
    · erw [hl₁, Category.assoc, hm₁]
    · erw [hm₂, hl₁']
#align category_theory.limits.right_square_is_pushout CategoryTheory.Limits.rightSquareIsPushout

end PasteLemma

section

variable {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)
variable [HasPullback f g] [HasPullback f' (pullback.fst : pullback f g ⟶ _)]
variable [HasPullback (f' ≫ f) g]

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g := by
  let this :=
    bigSquareIsPullback (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _)
      pullback.snd f' f pullback.fst pullback.fst g pullback.condition pullback.condition
      (pullbackIsPullback _ _) (pullbackIsPullback _ _)
  exact (this.conePointUniqueUpToIso (pullbackIsPullback _ _) : _)
#align category_theory.limits.pullback_right_pullback_fst_iso CategoryTheory.Limits.pullbackRightPullbackFstIso

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_hom_fst :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_hom_snd :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' := by
  rw [← pullback.condition]
  exact pullbackRightPullbackFstIso_inv_fst_assoc _ _ _ _
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst

end

section

variable {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)
variable [HasPushout f g] [HasPushout (pushout.inr : _ ⟶ pushout f g) g']
variable [HasPushout f (g ≫ g')]

/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ×[X] W` -/
noncomputable def pushoutLeftPushoutInrIso :
    pushout (pushout.inr : _ ⟶ pushout f g) g' ≅ pushout f (g ≫ g') :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).coconePointUniqueUpToIso
      (pushoutIsPushout _ _) :
    _)
#align category_theory.limits.pushout_left_pushout_inr_iso CategoryTheory.Limits.pushoutLeftPushoutInrIso

@[reassoc (attr := simp)]
theorem inl_pushoutLeftPushoutInrIso_inv :
    pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inl ≫ pushout.inl :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_inv
      (pushoutIsPushout _ _) WalkingSpan.left :
    _)
#align category_theory.limits.inl_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inl_pushoutLeftPushoutInrIso_inv

@[reassoc (attr := simp)]
theorem inr_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').hom = pushout.inr :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_hom
      (pushoutIsPushout _ _) WalkingSpan.right :
    _)
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_hom

@[reassoc (attr := simp)]
theorem inr_pushoutLeftPushoutInrIso_inv :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inr := by
  rw [Iso.comp_inv_eq, inr_pushoutLeftPushoutInrIso_hom]
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv

@[reassoc (attr := simp)]
theorem inl_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inl ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').hom = pushout.inl := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, inl_pushoutLeftPushoutInrIso_inv]
#align category_theory.limits.inl_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inl_inl_pushoutLeftPushoutInrIso_hom

@[reassoc (attr := simp)]
theorem inr_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').hom = g' ≫ pushout.inr := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, Category.assoc, inr_pushoutLeftPushoutInrIso_inv,
    pushout.condition]
#align category_theory.limits.inr_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_inl_pushoutLeftPushoutInrIso_hom

end

end CategoryTheory.Limits
