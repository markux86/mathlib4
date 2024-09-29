import Mathlib.CategoryTheory.Triangulated.Filtered.ForgetHalf

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

namespace FilteredTriangulated

variable {C : Type _} [Category C] [HasZeroObject C]  [Preadditive C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C] [IsTriangulated C]

variable [∀ (X : C) (n : ℤ), Decidable (IsZero ((Gr'' n).obj X))]

noncomputable def HalfForgetObj (X : C) : hP.Core' := by
  by_cases IsLE X 0
  · exact (existence_omega X).choose
  · exact 0

noncomputable def IdToHalfForgetApp (X : C) : X ⟶ (HalfForgetObj X).1 := by
  dsimp [HalfForgetObj]
  by_cases h : IsLE X 0
  · simp only [h, ↓reduceDIte]
    exact (existence_omega X).choose_spec.choose
  · simp only [h, ↓reduceDIte]
    exact 0

lemma HalfForgetObj_prop (X : C) [IsLE X 0] (Y : C) [IsGE Y 0] :
    Function.Bijective (fun (f : (HalfForgetObj X).1 ⟶ Y) ↦ (IdToHalfForgetApp X) ≫ f) := by
  dsimp [HalfForgetObj, IdToHalfForgetApp]
  have h : IsLE X 0 := inferInstance
  simp only [h, ↓reduceDIte, congrArg_cast_hom_right, assoc]
  refine Function.Bijective.comp ?_ (IsIso.comp_left_bijective _)
  exact (existence_omega X).choose_spec.choose_spec Y inferInstance

noncomputable def HalfForgetMap {X Y : C} (f : X ⟶ Y) : HalfForgetObj X ⟶ HalfForgetObj Y := by
  by_cases IsLE X 0
  · by_cases IsLE Y 0
    · exact ((HalfForgetObj_prop X (HalfForgetObj Y).1).2 (f ≫ IdToHalfForgetApp Y)).choose
    · exact 0
  · exact  0

@[simp]
lemma HalfForgetMap_prop {X Y : C} (f : X ⟶ Y) [IsLE X 0] [IsLE Y 0] :
    IdToHalfForgetApp X ≫ HalfForgetMap f = f ≫ IdToHalfForgetApp Y := by
  dsimp [HalfForgetMap]
  have hX : IsLE X 0 := inferInstance
  have hY : IsLE Y 0 := inferInstance
  simp only [hX, ↓reduceDIte, hY, ↓reduceIte]
  exact ((HalfForgetObj_prop X (HalfForgetObj Y).1).2 (f ≫ IdToHalfForgetApp Y)).choose_spec

lemma HalfForgetMapId {X : C} : HalfForgetMap (𝟙 X) = 𝟙 (HalfForgetObj X) := by
  by_cases h : IsLE X 0
  · apply (HalfForgetObj_prop X (HalfForgetObj X).1).1
    simp only
    rw [HalfForgetMap_prop (𝟙 X), id_comp]; erw [comp_id]
  · simp only [HalfForgetObj, h, HalfForgetMap, ↓reduceDIte]
    have : IsZero (HalfForgetObj X) := by
      simp only [HalfForgetObj, h, ↓reduceDIte]
      exact Limits.isZero_zero _
    exact (Limits.IsZero.eq_zero_of_src this _).symm

lemma HalfForgetMapComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsLE Y 0] :
    HalfForgetMap (f ≫ g) = HalfForgetMap f ≫ HalfForgetMap g := by
  have hY : IsLE Y 0 := inferInstance
  by_cases hX : IsLE X 0
  · by_cases hZ : IsLE Z 0
    · apply (HalfForgetObj_prop X (HalfForgetObj Z).1).1
      simp only
      rw [HalfForgetMap_prop (f ≫ g)]
      conv_rhs => erw [← assoc]; rw [HalfForgetMap_prop f, assoc, HalfForgetMap_prop g, ← assoc]
    · simp only [HalfForgetObj, hX, hZ, HalfForgetMap, ↓reduceDIte, hY, comp_zero]
  · simp only [HalfForgetObj, hX, HalfForgetMap, ↓reduceDIte, hY, dite_eq_ite, zero_comp]

lemma HalfForgetMapComp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hZ : ¬ (IsLE Z 0)) :
    HalfForgetMap (f ≫ g) = HalfForgetMap f ≫ HalfForgetMap g := by
  simp only [HalfForgetMap, hZ, ↓reduceDIte, dite_eq_ite, ite_self, comp_zero]

/- We construct `Forget X` as the colimit of `HalfForget X⟪n⟫` as `n` varies over `ℤ` (seen
as a poset category), with the transition maps given by `power_of_alpha`.-/

@[simp]
noncomputable def ForgetInductiveSystem_aux (X : C) : ℤ ⥤ C where
  obj a := (@shiftFunctor C _ _ _ Shift₂ a).obj X
  map := by
    intro a b f
    exact power_of_alpha X a b (b - a).natAbs
      (by rw [← Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom f)), add_sub_cancel])
  map_id a := by
    simp only [id_eq, eq_mpr_eq_cast, sub_self, Int.natAbs_zero]
    rw [power_of_alpha_zero', Iso.refl_hom]
  map_comp := by
    intro a b c f g
    simp only [id_eq, eq_mpr_eq_cast]
    have hab : (b - a).natAbs = b - a :=
      (Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom f))).symm
    have hbc : (c - b).natAbs = c - b :=
      (Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom g))).symm
    have hac : (c - a).natAbs = c - a :=
      (Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom (f ≫ g)))).symm
    rw [power_of_alpha_change_exponent X (c - a).natAbs ((b - a).natAbs + (c - b).natAbs)
      (by rw [← Nat.cast_inj (R := ℤ), Nat.cast_add, hab, hbc, hac, sub_add_sub_cancel'])
      a c (by rw [hac, add_sub_cancel])]
    exact (power_of_alpha_assoc X a b c (b - a).natAbs (c - b).natAbs
      (by rw [hab, add_sub_cancel]) (by rw [hbc, add_sub_cancel])).symm

noncomputable def ForgetInductiveSystem (X : C) : ℤ ⥤ hP.Core' where
  obj a := HalfForgetObj ((ForgetInductiveSystem_aux X).obj a)
  map f := HalfForgetMap ((ForgetInductiveSystem_aux X).map f)
  map_id a := by
    simp only
    rw [Functor.map_id, HalfForgetMapId]
  map_comp := by
    intro a b c f g
    simp only
    rw [Functor.map_comp]
    by_cases h : IsLE X (-b)
    · have : IsLE ((ForgetInductiveSystem_aux X).obj b) 0 := by
        dsimp [ForgetInductiveSystem_aux]
        exact isLE_shift X (-b) b 0 (by linarith)
      exact HalfForgetMapComp ((ForgetInductiveSystem_aux X).map f)
        ((ForgetInductiveSystem_aux X).map g)
    · have : ¬ IsLE ((ForgetInductiveSystem_aux X).obj c) 0 := by
        dsimp [ForgetInductiveSystem_aux]
        intro habs
        have : IsLE X (-c) := isLE_of_shift X (-c) c 0 (by linarith)
        have : IsLE X (-b ) := isLE_of_LE X (- c) (- b) (by have := leOfHom g; linarith)
        exact h this
      exact HalfForgetMapComp' ((ForgetInductiveSystem_aux X).map f)
        ((ForgetInductiveSystem_aux X).map g) this

lemma ForgetInductiveSystem_iso_of_le (X : C) (a : ℤ) [IsLE X a] {b c : Set.Iic (-a)}
    (u : b ⟶ c) : IsIso ((ForgetInductiveSystem X).map u) := by
  apply IsIso.mk
  set f : (ForgetInductiveSystem X).obj c.1 ⟶ (ForgetInductiveSystem X).obj b.1 := by
    have hX₁ : IsLE ((@shiftFunctor C _ _ _ Shift₂ c.1).obj X) 0 := sorry
    have hX₂ : IsLE ((@shiftFunctor C _ _ _ Shift₂ b.1).obj X) 0 := sorry
    simp only [ForgetInductiveSystem, ForgetInductiveSystem_aux]
    have := HalfForgetObj_prop ((@shiftFunctor C _ _ _ Shift₂ c.1).obj X)
      (HalfForgetObj ((@shiftFunctor C _ _ _ Shift₂ b.1).obj X)).1



noncomputable abbrev ForgetInductiveSystemMap {X Y : C} (f : X ⟶ Y) (a : ℤ) :
    (ForgetInductiveSystem X).obj a ⟶ (ForgetInductiveSystem Y).obj a :=
  HalfForgetMap ((@shiftFunctor C _ _ _ Shift₂ a).map f)

lemma ForgetInductiveSystemMap_naturality {X Y : C} (f : X ⟶ Y) {a b : ℤ} (u : a ⟶ b)
    [IsLE X (-b)] [IsLE Y (-b)] :
    (ForgetInductiveSystem X).map u ≫ ForgetInductiveSystemMap f b =
    ForgetInductiveSystemMap f a ≫ (ForgetInductiveSystem Y).map u := by
  dsimp [ForgetInductiveSystem, ForgetInductiveSystemMap]
  have : IsLE ((@shiftFunctor C _ _ _ Shift₂ b).obj X) 0 := isLE_shift X (-b) b 0 (by linarith)
  have : IsLE ((@shiftFunctor C _ _ _ Shift₂ a).obj Y) 0 := by
    have := isLE_shift Y (-b) a (a - b) (by linarith)
    exact isLE_of_LE _ (a - b) 0 (by have := leOfHom u; linarith)
  conv_lhs => rw [← HalfForgetMapComp]
  conv_rhs => rw [← HalfForgetMapComp]
  rw [power_of_alpha_naturality f]

/- The definition of the functor `Forget`.-/

noncomputable def ForgetObj (X : C) : hP.Core' := sorry
    --Limits.limit (ForgetInductiveSystem X)
    --need to prove that this has a limit, use CategoryTheory.Functor.Initial.limitIso',
    -- CategoryTheory.Functor.Initial.hasLimit_of_comp and the fact that all transition
    -- maps are isos for `a` small enough.

end FilteredTriangulated

end Triangulated

end CategoryTheory
