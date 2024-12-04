/-
Copyright (c) 2024 Christoper Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Sym.Sym2

/-!
# Sym2 (ι₁ × ι₂)

-/

section Prod

variable {ι₁ : Type*}
variable {ι₂ : Type*}

/-- Off the diagonal in both components -/
def symOffDiag : Sym2 (ι₁ × ι₂) → Prop := Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => i₁ ≠ j₁ ∧ i₂ ≠ j₂, by
  aesop⟩

theorem mk_symOffDiag_iff {x y : (ι₁ × ι₂)} : symOffDiag s(x, y) ↔ x.1 ≠ y.1 ∧ x.2 ≠ y.2 :=
  Iff.rfl


@[simp]
theorem symOffDiag_iff_proj_eq (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiag (Sym2.mk z) ↔ z.1.1 ≠ z.2.1 ∧ z.1.2 ≠ z.2.2 :=
  Prod.recOn z fun _ _ => mk_symOffDiag_iff


instance symOffDiag.decidablePred [DecidableEq ι₁] [DecidableEq ι₂] :
    DecidablePred (@symOffDiag ι₁ ι₂) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiag_iff_proj_eq a)

/-- Triangular -/
def symOffDiagUpper [LT ι₁] [LT ι₂] : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => (i₁ < j₁ ∧ i₂ < j₂) ∨ j₁ < i₁ ∧ j₂ < i₂, by aesop⟩

--variable [LT ι₁] [LT ι₂]

theorem mk_symOffDiagUpper_iff [LT ι₁] [LT ι₂] {i j : (ι₁ × ι₂)} :
    symOffDiagUpper s(i, j) ↔ (i.1 < j.1 ∧ i.2 < j.2) ∨ j.1 < i.1 ∧ j.2 < i.2 :=
  Iff.rfl

@[simp]
theorem symOffDiagUpper_iff_proj_eq [LT ι₁] [LT ι₂] (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagUpper (Sym2.mk z) ↔ (z.1.1 < z.2.1 ∧ z.1.2 < z.2.2) ∨ z.2.1 < z.1.1 ∧ z.2.2 < z.1.2 :=
  Prod.recOn z fun _ _ => mk_symOffDiagUpper_iff

/- Can probably weaken the hypothesis here -/
instance symOffDiagUpper.decidablePred [LinearOrder ι₁] [LinearOrder ι₂] :
    DecidablePred (@symOffDiagUpper ι₁ ι₂ _ _) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagUpper_iff_proj_eq a)

/-- Triangular -/
def symOffDiagLower [LT ι₁] [LT ι₂] : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => (i₁ < j₁ ∧ j₂ < i₂) ∨ j₁ < i₁ ∧ i₂ < j₂, by aesop⟩

--variable [LT ι₁] [LT ι₂]

theorem mk_symOffDiagLower_iff [LT ι₁] [LT ι₂] {i j : (ι₁ × ι₂)} :
    symOffDiagLower s(i, j) ↔ (i.1 < j.1 ∧ j.2 < i.2) ∨ j.1 < i.1 ∧ i.2 < j.2 :=
  Iff.rfl

@[simp]
theorem symOffDiagLower_iff_proj_eq [LT ι₁] [LT ι₂] (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagLower (Sym2.mk z) ↔ (z.1.1 < z.2.1 ∧ z.2.2 < z.1.2) ∨ z.2.1 < z.1.1 ∧ z.1.2 < z.2.2 :=
  Prod.recOn z fun _ _ => mk_symOffDiagLower_iff

/- Can probably weaken the hypothesis here -/
instance symOffDiagLower.decidablePred [LinearOrder ι₁] [LinearOrder ι₂] :
    DecidablePred (@symOffDiagLower ι₁ ι₂ _ _) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagLower_iff_proj_eq a)

/--
Exactly one pair of coordinates are equal
-/
def symOffDiagXor : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => Xor' (i₁ = j₁) (i₂ = j₂), by
    intro ⟨i₁, j₁⟩  ⟨i₂, j₂⟩
    simp_all only [eq_iff_iff]
    apply Iff.intro
    · intro a
      apply a.imp
      · aesop
      · aesop
    · intro a
      apply a.imp
      · aesop
      · aesop⟩

theorem mk_symOffDiagXor_iff {i j : (ι₁ × ι₂)} :
    symOffDiagXor s(i, j) ↔ Xor' (i.1 = j.1) (i.2 = j.2) := Iff.rfl

@[simp]
theorem symOffDiagXor_iff_proj_eq (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagXor (Sym2.mk z) ↔ Xor' (z.1.1 = z.2.1) (z.1.2 = z.2.2) :=
  Prod.recOn z fun _ _ => mk_symOffDiagXor_iff

instance symOffDiagXor.decidablePred [DecidableEq ι₁] [DecidableEq ι₂] :
    DecidablePred (@symOffDiagXor ι₁ ι₂) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagXor_iff_proj_eq a)

/--
Left coord equal, right not-equal
-/
def symOffDiagLeft : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => (i₁ = j₁) ∧ ¬ (i₂ = j₂), by aesop⟩

theorem mk_symOffDiagLeft_iff {i j : (ι₁ × ι₂)} :
    symOffDiagLeft s(i, j) ↔ (i.1 = j.1) ∧ ¬ (i.2 = j.2) := Iff.rfl

@[simp]
theorem symOffDiagLeft_iff_proj_eq (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagLeft (Sym2.mk z) ↔ (z.1.1 = z.2.1) ∧ ¬(z.1.2 = z.2.2) :=
  Prod.recOn z fun _ _ => mk_symOffDiagLeft_iff

instance symOffDiagLeft.decidablePred [DecidableEq ι₁] [DecidableEq ι₂] :
    DecidablePred (@symOffDiagLeft ι₁ ι₂) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagLeft_iff_proj_eq a)

/--
Right coord equal, left not-equal
-/
def symOffDiagRight : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => (i₂ = j₂) ∧ ¬(i₁ = j₁), by aesop⟩

theorem mk_symOffDiagRight_iff {i j : (ι₁ × ι₂)} :
    symOffDiagRight s(i, j) ↔ (i.2 = j.2) ∧ ¬(i.1 = j.1)  := Iff.rfl

@[simp]
theorem symOffDiagRight_iff_proj_eq (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagRight (Sym2.mk z) ↔ (z.1.2 = z.2.2) ∧ ¬(z.1.1 = z.2.1) :=
  Prod.recOn z fun _ _ => mk_symOffDiagRight_iff

instance symOffDiagRight.decidablePred [DecidableEq ι₁] [DecidableEq ι₂] :
    DecidablePred (@symOffDiagRight ι₁ ι₂) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagRight_iff_proj_eq a)

lemma f1 (p : Sym2 (ι₁ × ι₂)) : Xor' p.IsDiag ¬ p.IsDiag :=
  xor_not_right.mpr (Eq.to_iff rfl)

lemma foo [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagUpper p) :
    symOffDiag p := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma foo2 [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagLower p) :
    symOffDiag p := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : symOffDiag p ↔ Xor' (symOffDiagUpper p) (symOffDiagLower p) := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  constructor
  · intro h
    simp_all only [symOffDiag_iff_proj_eq, ne_eq, symOffDiagUpper_iff_proj_eq,
      symOffDiagLower_iff_proj_eq]
    obtain ⟨left, right⟩ := h
    have ee1 : Xor' (i₁ < j₁) (j₁ < i₁) := by
      rw [xor_iff_or_and_not_and]
      constructor
      · aesop
      · simp
        exact fun a ↦ le_of_lt a
    have ee2 : Xor' (i₂ < j₂) (j₂ < i₂) := by
      rw [xor_iff_or_and_not_and]
      constructor
      · aesop
      · simp
        exact fun a ↦ le_of_lt a
    rcases ee1 with (h | h')
    · rcases ee2 with (g | g')
      · aesop
      · rw [xor_iff_or_and_not_and]
        aesop
    · rcases ee2 with (g | g')
      · rw [xor_iff_or_and_not_and]
        aesop
      · aesop
  · intro h
    aesop

lemma foo3 (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagXor p) :
    ¬ p.IsDiag := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma foo4 (p : Sym2 (ι₁ × ι₂)) (h : symOffDiag p) :
    ¬ p.IsDiag := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma not_IsDiag_iff_symOffDiagXor_xor_symOffDiag (p : Sym2 (ι₁ × ι₂)) :
    ¬ p.IsDiag ↔ Xor' (symOffDiagXor p) (symOffDiag p) := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  rw [xor_iff_or_and_not_and]
  constructor
  · intro h
    simp_all only [Sym2.isDiag_iff_proj_eq, Prod.mk.injEq, not_and,
      symOffDiagXor_iff_proj_eq, symOffDiag_iff_proj_eq, ne_eq, Decidable.not_not]
    apply And.intro
    · rw [xor_iff_or_and_not_and]
      simp_all only [not_and, not_false_eq_true, implies_true, and_true]
      have e1 : i₁ = j₁ ∨ ¬ i₁ = j₁ := eq_or_ne i₁ j₁
      cases' e1 with h1 h2
      · apply Or.inl
        apply Or.inl h1
      · cases' (eq_or_ne i₂ j₂) with h3 h4
        · apply Or.inl
          apply Or.inr h3
        · apply Or.inr
          constructor
          · exact h2
          · apply h4
    · intro h1 h2
      aesop
  · intro h
    aesop

lemma not_symOffDiagXor_and_symOffDiag (p : Sym2 (ι₁ × ι₂)) :
    ¬((symOffDiagXor p) ∧ (symOffDiag p)) := by
  simp only [not_and]
  intro h
  have e1 : ¬ p.IsDiag := foo3 p h
  rw [not_IsDiag_iff_symOffDiagXor_xor_symOffDiag] at e1
  simp_all only [xor_true, not_false_eq_true]

lemma not_symOffDiagUpper_and_symOffDiagLower [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) :
    ¬((symOffDiagUpper p) ∧ (symOffDiagLower p)) := by
  simp only [not_and]
  intro h
  have e1 : symOffDiag p := by exact foo p h
  rw [symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower] at e1
  simp_all only [xor_true, not_false_eq_true]


lemma e1 (p : Sym2 (ι₁ × ι₂)) : symOffDiagXor p ∧ ¬symOffDiag p ↔ symOffDiagXor p := by
  constructor
  · intro h
    aesop
  · intro h
    constructor
    · exact h
    · by_contra h'
      have t1 : (symOffDiagXor p) ∧ (symOffDiag p) := by exact ⟨h, h'⟩
      have f1 : ¬((symOffDiagXor p) ∧ (symOffDiag p))  :=
        not_symOffDiagXor_and_symOffDiag p
      exact f1 t1

-- symOffDiag x ∧ ¬symOffDiagXor x)

lemma e2 (p : Sym2 (ι₁ × ι₂)) : symOffDiag p ∧ ¬symOffDiagXor p ↔ symOffDiag p := by
  constructor
  · intro h
    aesop
  · intro h
    constructor
    · exact h
    · by_contra h'
      have t1 : (symOffDiagXor p) ∧ (symOffDiag p) := by exact ⟨h', h⟩
      have f1 : ¬((symOffDiagXor p) ∧ (symOffDiag p))  :=
        not_symOffDiagXor_and_symOffDiag p
      exact f1 t1

lemma e3 (p : Sym2 (ι₁ × ι₂)) [LinearOrder ι₁] [LinearOrder ι₂] :
    symOffDiagLower p ∧ ¬symOffDiagUpper p ↔ symOffDiagLower p := by
  constructor
  · intro h
    aesop
  · intro h
    constructor
    · exact h
    · by_contra h'
      have t1 : (symOffDiagLower p) ∧ (symOffDiagUpper p) := by exact ⟨h, h'⟩
      have f1 : ¬((symOffDiagLower p) ∧ (symOffDiagUpper p))  := by
        rw [and_comm]
        exact not_symOffDiagUpper_and_symOffDiagLower p
      exact f1 t1

lemma e4 (p : Sym2 (ι₁ × ι₂)) [LinearOrder ι₁] [LinearOrder ι₂] :
    symOffDiagUpper p ∧ ¬symOffDiagLower p ↔ symOffDiagUpper p := by
  constructor
  · intro h
    aesop
  · intro h
    constructor
    · exact h
    · by_contra h'
      have t1 : (symOffDiagLower p) ∧ (symOffDiagUpper p) := by exact ⟨h', h⟩
      have f1 : ¬((symOffDiagLower p) ∧ (symOffDiagUpper p))  := by
        rw [and_comm]
        exact not_symOffDiagUpper_and_symOffDiagLower p
      exact f1 t1

end Prod
