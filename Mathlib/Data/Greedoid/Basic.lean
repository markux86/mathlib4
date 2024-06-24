/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic

/-!
This file contains the definition of `ExchangeProperty` and `AccessibleProperty`, along with the
main subject `Greedoid α`.

# Greedoid
Greedoid is a set system, i.e., a family of sets, over a finite ground set, which satisfies both
exchange and accessible properties.

## Exchange Property and Accessible Property of Greedoid
If a set system `S` satisfies the exchange property, then there is some element `x ∈ s₂ \ s₁`
which `s₁ ∪ {x} ∈ S`, for every set `s₁, s₂ ∈ S` satisfying `s₁.card < s₂.card`.
If a set system `S` satisfies the accessible property, then there is some element `x ∈ s`
which `s \ {x} ∈ S` for every nonempty set `s ∈ S`.
These two properties are defined in this file as `ExchangeProperty` and `AccessibleProperty`.
-/

namespace Greedoid

open Nat Finset

/-- The exchange property of greedoid.
    Note that the exchange property also hold for (finite) matroids. -/
def ExchangeProperty {α : Type*} (Sys : Finset (Finset α)) :=
  ⦃s₁ : Finset α⦄ → s₁ ∈ Sys →
  ⦃s₂ : Finset α⦄ → s₂ ∈ Sys →
  s₂.card < s₁.card →
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, cons x s₂ h ∈ Sys

/-- A set system satisfies the exchange property if there is some element `x` in some feasible
    `s₁` which is not in `s₂` with smaller cardinality, and `s₂ ∪ {x}` is also feasible.
    This implies that all maximal feasible sets are actually maximum. -/
class Exchange {α : Type*} (Sys : Finset (Finset α)) : Prop :=
  exchange :
    ⦃s₁ : Finset α⦄ → s₁ ∈ Sys →
    ⦃s₂ : Finset α⦄ → s₂ ∈ Sys →
    s₂.card < s₁.card →
      ∃ x ∈ s₁, ∃ h : x ∉ s₂, cons x s₂ h ∈ Sys

instance {α : Type*} [DecidableEq α] :
    @DecidablePred (Finset (Finset α)) ExchangeProperty :=
  λ Sys ↦ by unfold ExchangeProperty; infer_instance

/-- The accessible property of greedoid -/
def AccessibleProperty {α : Type*} (Sys : Finset (Finset α)) : Prop :=
  ⦃s : Finset α⦄ → s ∈ Sys → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ Sys

/-- A set system is accessible if there is some element `x` in `s` which `s \ {x}` is also in the
    set system, for each nonempty set `s` of the set system.
    This automatically implies that nonempty accessible set systems contain an empty set. -/
class Accessible {α : Type*} (Sys : Finset (Finset α)) : Prop where
  accessible : ⦃s : Finset α⦄ → s ∈ Sys → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ Sys

end Greedoid

/-- Greedoid is a nonempty (finite) set system satsifying both accessible and exchange property. -/
structure Greedoid (α : Type*) where
  /-- The ground set which every element lies on. -/
  ground_set : Finset α
  /-- The feasible set of the greedoid. -/
  feasible_set : Finset (Finset α)
  contains_emptyset : ∅ ∈ feasible_set
  accessible_property : Greedoid.AccessibleProperty feasible_set
  exchange_property : Greedoid.ExchangeProperty feasible_set
  subset_ground : ∀ s ∈ feasible_set, s ⊆ ground_set

section Greedoid

variable {α : Type*}

/-- Definition of `Finset` in `Greedoid`.
    This is often called 'feasible'· -/
protected def Greedoid.mem (s : Finset α) (G : Greedoid α) := s ∈ G.feasible_set

instance : Membership (Finset α) (Greedoid α) :=
  ⟨Greedoid.mem⟩

instance [DecidableEq α] {G : Greedoid α} : DecidablePred (λ s ↦ s ∈ G) := λ s ↦
  if h : s ∈ G.feasible_set
    then isTrue h
    else isFalse λ h' ↦ h h'

end Greedoid

namespace Greedoid

variable {α : Type*}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
    G₁.ground_set = G₂.ground_set → G₁.feasible_set = G₂.feasible_set → G₁ = G₂
  | ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

@[simp]
theorem feasible_set_injective :
    Function.Injective (λ G : Greedoid α ↦ (G.ground_set, G.feasible_set)) :=
  λ _ _ ↦ by simp; exact eq_of_veq

@[simp]
theorem feasible_set_inj {G₁ G₂ : Greedoid α} :
    G₁.ground_set = G₂.ground_set ∧ G₁.feasible_set = G₂.feasible_set ↔ G₁ = G₂ :=
  ⟨λ h ↦ by apply eq_of_veq <;> simp [h], λ h ↦ by simp [h]⟩

instance [DecidableEq α] : DecidableEq (Greedoid α) := λ G₁ G₂ ↦
  if h₁ : G₁.ground_set = G₂.ground_set
    then if h₂ : G₁.feasible_set = G₂.feasible_set
      then isTrue (eq_of_veq h₁ h₂)
      else isFalse (λ h' ↦ h₂ (h' ▸ rfl))
    else isFalse (λ h' ↦ h₁ (h' ▸ rfl))

variable {G : Greedoid α}

instance : Exchange G.feasible_set := ⟨G.exchange_property⟩

instance : Accessible G.feasible_set := ⟨G.accessible_property⟩

section Membership

@[simp]
theorem system_feasible_set_mem_mem {s : Finset α} : s ∈ G.feasible_set ↔ s ∈ G := by rfl

theorem mem_accessible {s : Finset α} (hs₁ : s ∈ G.feasible_set) (hs₂ : s.Nonempty) :
    ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ t ∈ G :=
  G.accessible_property hs₁ hs₂

theorem mem_exchange
    {s₁ : Finset α} (hs₁ : s₁ ∈ G)
    {s₂ : Finset α} (hs₂ : s₂ ∈ G)
    (hs : s₂.card < s₁.card) :
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, cons x s₂ h ∈ G :=
  G.exchange_property hs₁ hs₂ hs

instance [DecidableEq α] : DecidablePred (· ∈ G) := λ x ↦ by
  infer_instance

end Membership

@[simp]
theorem greedoid_nonempty : G.feasible_set.Nonempty := ⟨∅, G.contains_emptyset⟩

instance : Nonempty G.feasible_set := ⟨∅, G.contains_emptyset⟩

section Exchange

variable {α : Type*}
variable {Sys : Finset (Finset α)} [Exchange Sys]
variable {s₁ : Finset α} (hs₁ : s₁ ∈ Sys)
variable {s₂ : Finset α} (hs₂ : s₂ ∈ Sys)

-- TODO: Find better name.
theorem exchangeProperty_exists_superset_of_card_le
    {n : ℕ} (hn₁ : n ≤ s₁.card) (hn₂ : s₂.card ≤ n) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ (∀ e ∈ s, e ∈ s₁ ∨ e ∈ s₂) ∧ s.card = n := by
  induction n, hn₂ using le_induction with
  | base => use s₂; simp [hs₂]; intro _ h; exact Or.inr h
  | succ n hn ihn =>
    rcases ihn (by omega) with ⟨s, hs, h₁, h₂, rfl⟩
    rcases Exchange.exchange hs₁ hs hn₁ with ⟨x, hx₁, hx₂, hx₃⟩
    use cons x s hx₂
    simp [*]; exact ⟨Finset.Subset.trans h₁ (Finset.subset_cons hx₂), h₂⟩

-- TODO: Find better name.
theorem exchangeProperty_exists_feasible_superset_add_element_feasible'
    (hs : s₂ ⊆ s₁)
    {n : ℕ} (hn : n = s₁.card - s₂.card)
    {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ s ⊆ s₁ ∧ ∃ h : a ∉ s, cons a s h ∈ Sys := by
  induction n generalizing s₂ with
  | zero =>
    exact False.elim ((eq_of_subset_of_card_le hs (Nat.le_of_sub_eq_zero hn.symm) ▸ ha₂) ha₁)
  | succ n ih =>
    rcases exchangeProperty_exists_superset_of_card_le hs₁ hs₂ (by omega) (le_succ _)
      with ⟨s, hs₁, hs₂, hs₃, hs₄⟩
    by_cases h : a ∈ s
    · use s₂; simp [*]
      rw [eq_of_subset_of_card_le (cons_subset.2 ⟨h, hs₂⟩) (by simp at hs₄; simp [hs₄])]
      exact hs₁
    · rcases ih hs₁ (λ _ h ↦ by apply Or.elim (hs₃ _ h) <;> tauto) (by omega) (by simp [*])
        with ⟨t, ht₁, ht₂, ht₃, ht₄, ht₅⟩
      use t; simp_all [Finset.Subset.trans hs₂]

theorem exchangeProperty_exists_feasible_superset_add_element_feasible
    (hs : s₂ ⊆ s₁) {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ s ⊆ s₁ ∧ ∃ h : a ∉ s, cons a s h ∈ Sys :=
  exchangeProperty_exists_feasible_superset_add_element_feasible' hs₁ hs₂ hs rfl ha₁ ha₂

end Exchange

section Accessible

variable {α : Type*}
variable {Sys : Finset (Finset α)} [Accessible Sys]

theorem accessible_nonempty_contains_emptyset'
    {s : Finset α} (hs : s ∈ Sys) {n : ℕ} (hn : n = s.card) :
    ∅ ∈ Sys := by
  induction n generalizing s with
  | zero => exact card_eq_zero.mp hn.symm ▸ hs
  | succ _ ih =>
    rcases Accessible.accessible hs (by rw [← Finset.card_ne_zero]; omega)
      with ⟨t, _, _, ht⟩
    exact ih ht (by omega)

theorem accessible_nonempty_contains_emptyset [Nonempty Sys] : ∅ ∈ Sys :=
  have ⟨_, hs⟩ := nonempty_coe_sort.mp ‹Nonempty Sys›
  accessible_nonempty_contains_emptyset' hs rfl

-- TODO: Find better name.
theorem induction_on_accessible' [Nonempty Sys]
    {p : (s : Finset α) → s ∈ Sys → Prop}
    (empty : p ∅ accessible_nonempty_contains_emptyset)
    (insert : ∀ ⦃s₁ : Finset α⦄, (hs₁ : s₁ ∈ Sys) →
    ∀ ⦃s₂ : Finset α⦄, (hs₂ : s₂ ∈ Sys) →
    s₂ ⊆ s₁ → s₂.card + 1 = s₁.card → p s₂ hs₂ → p s₁ hs₁)
    (s : Finset α) (hs : s ∈ Sys) {n : ℕ} (hn : n = s.card) :
    p s hs := by
  induction n generalizing s with
  | zero => exact card_eq_zero.mp hn.symm ▸ empty
  | succ n ih =>
    rcases Accessible.accessible hs (by rw [← Finset.card_ne_zero]; omega)
      with ⟨_, ht₁, ht₂, ht₃⟩
    exact insert hs ht₃ ht₁ ht₂ (ih _ ht₃ (by omega))

-- TODO: Find better name.
theorem induction_on_accessible [Nonempty Sys]
    {p : (s : Finset α) → s ∈ Sys → Prop} (empty : p ∅ accessible_nonempty_contains_emptyset)
    (insert : ∀ ⦃s₁ : Finset α⦄, (hs₁ : s₁ ∈ Sys) →
    ∀ ⦃s₂ : Finset α⦄, (hs₂ : s₂ ∈ Sys) →
    s₂ ⊆ s₁ → s₂.card + 1 = s₁.card → p s₂ hs₂ → p s₁ hs₁) :
    ∀ (s : Finset α) (hs : s ∈ Sys), p s hs
  | s, hs => induction_on_accessible' empty insert s hs rfl

-- TODO: Find better name.
theorem construction_on_accessible [Nonempty Sys]
    {s : Finset α} (hs : s ∈ Sys) :
    ∃ l : List α, l.Nodup ∧ Multiset.ofList l = s.val ∧ ∀ l', l' <:+ l →
      ∃ s' : Finset α, Multiset.ofList l' = s'.val ∧ s' ∈ Sys := by
  induction s, hs using induction_on_accessible with
  | empty => use []; simp; use ∅; simp [accessible_nonempty_contains_emptyset]
  | insert h₁ _ h₂ h₃ h₄ =>
    rcases h₄ with ⟨l, h₄, h₅, h₆⟩
    rcases ssubset_iff_exists_cons_subset.mp
      ⟨h₂, λ h' ↦ by have := subset_antisymm h' h₂ ▸ h₃; omega⟩ with ⟨a, ha₁, ha₂⟩
    use a :: l
    have hal : (a :: l).Nodup := by
      simp [h₄]; intro h'; apply ha₁; rw [Finset.mem_def, ← h₅]; exact h'
    have has := (eq_of_subset_of_card_le ha₂ (le_of_eq (h₃ ▸ card_cons ha₁).symm)
      ▸ (cons_val ha₁).symm ▸ Multiset.cons_coe a l ▸ (Multiset.cons_inj_right a).mpr h₅)
    apply And.intro hal (And.intro has _)
    intro l' h₇; use ⟨Multiset.ofList l', Nodup.sublist (IsSuffix.sublist h₇) hal⟩
    simp; rw [suffix_cons_iff] at h₇; apply Or.elim h₇ <;> intro h₇
    · simp [h₇, has, h₁]
    · rcases h₆ l' h₇ with ⟨_, ht₁, ht₂⟩; simp only [ht₁, ht₂]

end Accessible

/-- To prove a proposition on each feasible set `s : Finset α` of a greedoid `G : Greedoid α`,
    it suffices to prove it for the emptyset, and to show that if it holds for some `t ∈ G`,
    then it holds for `s = cons a t _` which `s ∈ G`. -/
protected theorem induction_on {p : Finset α → Prop} (empty : p ∅)
    (insert : ∀ ⦃a : α⦄ {t : Finset α} (ha : a ∉ t), cons a t ha ∈ G → p t → p (cons a t ha))
    {s : Finset α} (hs : s ∈ G) :
    p s := by
  induction s , hs using induction_on_accessible with
  | empty => exact empty
  | insert h₁ _ h₂ h₃ h₄ =>
    rcases ssubset_iff_exists_cons_subset.mp (Finset.ssubset_iff_subset_ne.mpr
      ⟨h₂, λ h ↦ by simp [h] at h₃⟩) with ⟨_, _, ha⟩
    have h := eq_of_subset_of_card_le ha (le_of_eq (by simp [h₃]))
    exact h.symm ▸ insert _ (h ▸ h₁) h₄

end Greedoid
