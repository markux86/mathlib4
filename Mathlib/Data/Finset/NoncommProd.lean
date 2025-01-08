/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Data.Fintype.Card

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `Finset.prod` and `Multiset.prod` require `[CommMonoid α]`.
Often, there are collections `s : Finset α` where `[Monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), Commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `Finset.noncommProd`, requiring a proof of commutativity of held terms
- `Multiset.noncommProd`, requiring a proof of commutativity of held terms

## Implementation details

While `List.prod` is defined via `List.foldl`, `noncommProd` is defined via
`Multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

TODO: Tidy up this file by using the fact that the submonoid generated by commuting
elements is commutative and using the `Finset.prod` versions of lemmas to prove the `noncommProd`
version.
-/

variable {F ι α β γ : Type*} (f : α → β → β) (op : α → α → α)

namespace Multiset

/-- Fold of a `s : Multiset α` with `f : α → β → β`, given a proof that `LeftCommutative f`
on all elements `x ∈ s`. -/
def noncommFoldr (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise fun x y => ∀ b, f x (f y b) = f y (f x b)) (b : β) : β :=
  letI : LeftCommutative (α := { x // x ∈ s }) (f ∘ Subtype.val) :=
    ⟨fun ⟨_, hx⟩ ⟨_, hy⟩ =>
      haveI : IsRefl α fun x y => ∀ b, f x (f y b) = f y (f x b) := ⟨fun _ _ => rfl⟩
      comm.of_refl hx hy⟩
  s.attach.foldr (f ∘ Subtype.val) b

@[simp]
theorem noncommFoldr_coe (l : List α) (comm) (b : β) :
    noncommFoldr f (l : Multiset α) comm b = l.foldr f b := by
  simp only [noncommFoldr, coe_foldr, coe_attach, List.attach, List.attachWith, Function.comp_def]
  rw [← List.foldr_map]
  simp [List.map_pmap]

@[simp]
theorem noncommFoldr_empty (h) (b : β) : noncommFoldr f (0 : Multiset α) h b = b :=
  rfl

theorem noncommFoldr_cons (s : Multiset α) (a : α) (h h') (b : β) :
    noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b) := by
  induction s using Quotient.inductionOn
  simp

theorem noncommFoldr_eq_foldr (s : Multiset α) [h : LeftCommutative f] (b : β) :
    noncommFoldr f s (fun x _ y _ _ => h.left_comm x y) b = foldr f b s := by
  induction s using Quotient.inductionOn
  simp

section assoc

variable [assoc : Std.Associative op]

/-- Fold of a `s : Multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncommFold (s : Multiset α) (comm : { x | x ∈ s }.Pairwise fun x y => op x y = op y x) :
    α → α :=
  noncommFoldr op s fun x hx y hy h b => by rw [← assoc.assoc, comm hx hy h, assoc.assoc]

@[simp]
theorem noncommFold_coe (l : List α) (comm) (a : α) :
    noncommFold op (l : Multiset α) comm a = l.foldr op a := by simp [noncommFold]

@[simp]
theorem noncommFold_empty (h) (a : α) : noncommFold op (0 : Multiset α) h a = a :=
  rfl

theorem noncommFold_cons (s : Multiset α) (a : α) (h h') (x : α) :
    noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x) := by
  induction s using Quotient.inductionOn
  simp

theorem noncommFold_eq_fold (s : Multiset α) [Std.Commutative op] (a : α) :
    noncommFold op s (fun x _ y _ _ => Std.Commutative.comm x y) a = fold op a s := by
  induction s using Quotient.inductionOn
  simp

end assoc

variable [Monoid α] [Monoid β]

/-- Product of a `s : Multiset α` with `[Monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      "Sum of a `s : Multiset α` with `[AddMonoid α]`, given a proof that `+` commutes
      on all elements `x ∈ s`."]
def noncommProd (s : Multiset α) (comm : { x | x ∈ s }.Pairwise Commute) : α :=
  s.noncommFold (· * ·) comm 1

@[to_additive (attr := simp)]
theorem noncommProd_coe (l : List α) (comm) : noncommProd (l : Multiset α) comm = l.prod := by
  rw [noncommProd]
  simp only [noncommFold_coe]
  induction' l with hd tl hl
  · simp
  · rw [List.prod_cons, List.foldr, hl]
    intro x hx y hy
    exact comm (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)

@[to_additive (attr := simp)]
theorem noncommProd_empty (h) : noncommProd (0 : Multiset α) h = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem noncommProd_cons (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = a * noncommProd s (comm.mono fun _ => mem_cons_of_mem) := by
  induction s using Quotient.inductionOn
  simp

@[to_additive]
theorem noncommProd_cons' (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = noncommProd s (comm.mono fun _ => mem_cons_of_mem) * a := by
  induction' s using Quotient.inductionOn with s
  simp only [quot_mk_to_coe, cons_coe, noncommProd_coe, List.prod_cons]
  induction' s with hd tl IH
  · simp
  · rw [List.prod_cons, mul_assoc, ← IH, ← mul_assoc, ← mul_assoc]
    · congr 1
      apply comm.of_refl <;> simp
    · intro x hx y hy
      simp only [quot_mk_to_coe, List.mem_cons, mem_coe, cons_coe] at hx hy
      apply comm
      · cases hx <;> simp [*]
      · cases hy <;> simp [*]

@[to_additive]
theorem noncommProd_add (s t : Multiset α) (comm) :
    noncommProd (s + t) comm =
      noncommProd s (comm.mono <| subset_of_le <| s.le_add_right t) *
        noncommProd t (comm.mono <| subset_of_le <| t.le_add_left s) := by
  rcases s with ⟨⟩
  rcases t with ⟨⟩
  simp

@[to_additive]
lemma noncommProd_induction (s : Multiset α) (comm)
    (p : α → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p x) :
    p (s.noncommProd comm) := by
  induction' s using Quotient.inductionOn with l
  simp only [quot_mk_to_coe, noncommProd_coe, mem_coe] at base ⊢
  exact l.prod_induction p hom unit base

variable [FunLike F α β]

@[to_additive]
protected theorem map_noncommProd_aux [MonoidHomClass F α β] (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise Commute) (f : F) : { x | x ∈ s.map f }.Pairwise Commute := by
  simp only [Multiset.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
  exact (comm.of_refl hx hy).map f

@[to_additive]
theorem map_noncommProd [MonoidHomClass F α β] (s : Multiset α) (comm) (f : F) :
    f (s.noncommProd comm) = (s.map f).noncommProd (Multiset.map_noncommProd_aux s comm f) := by
  induction s using Quotient.inductionOn
  simpa using map_list_prod f _

@[deprecated (since := "2024-07-23")] alias noncommProd_map := map_noncommProd
@[deprecated (since := "2024-07-23")] alias noncommSum_map := map_noncommSum
@[deprecated (since := "2024-07-23")]
protected alias noncommProd_map_aux := Multiset.map_noncommProd_aux
@[deprecated (since := "2024-07-23")]
protected alias noncommSum_map_aux := Multiset.map_noncommSum_aux

@[to_additive noncommSum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Multiset α) (comm) (m : α) (h : ∀ x ∈ s, x = m) :
    s.noncommProd comm = m ^ Multiset.card s := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncommProd_coe, coe_card, mem_coe] at *
  exact List.prod_eq_pow_card _ m h

@[to_additive]
theorem noncommProd_eq_prod {α : Type*} [CommMonoid α] (s : Multiset α) :
    (noncommProd s fun _ _ _ _ _ => Commute.all _ _) = prod s := by
  induction s using Quotient.inductionOn
  simp

@[to_additive]
theorem noncommProd_commute (s : Multiset α) (comm) (y : α) (h : ∀ x ∈ s, Commute y x) :
    Commute y (s.noncommProd comm) := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncommProd_coe]
  exact Commute.list_prod_right _ _ h

theorem mul_noncommProd_erase [DecidableEq α] (s : Multiset α) {a : α} (h : a ∈ s) (comm)
    (comm' := fun _ hx _ hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    a * (s.erase a).noncommProd comm' = s.noncommProd comm := by
  induction' s using Quotient.inductionOn with l
  simp only [quot_mk_to_coe, mem_coe, coe_erase, noncommProd_coe] at comm h ⊢
  suffices ∀ x ∈ l, ∀ y ∈ l, x * y = y * x by rw [List.prod_erase_of_comm h this]
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  exact comm hx hy hxy

theorem noncommProd_erase_mul [DecidableEq α] (s : Multiset α) {a : α} (h : a ∈ s) (comm)
    (comm' := fun _ hx _ hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    (s.erase a).noncommProd comm' * a = s.noncommProd comm := by
  suffices ∀ b ∈ erase s a, Commute a b by
    rw [← (noncommProd_commute (s.erase a) comm' a this).eq, mul_noncommProd_erase s h comm comm']
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · rfl
  exact comm h (mem_of_mem_erase hb) hab

end Multiset

namespace Finset

variable [Monoid β] [Monoid γ]

open scoped Function -- required for scoped `on` notation

/-- Proof used in definition of `Finset.noncommProd` -/
@[to_additive]
theorem noncommProd_lemma (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise (Commute on f)) :
    Set.Pairwise { x | x ∈ Multiset.map f s.val } Commute := by
  simp_rw [Multiset.mem_map]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
  exact comm.of_refl ha hb

/-- Product of a `s : Finset α` mapped with `f : α → β` with `[Monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive
      "Sum of a `s : Finset α` mapped with `f : α → β` with `[AddMonoid β]`,
given a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncommProd (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise (Commute on f)) : β :=
  (s.1.map f).noncommProd <| noncommProd_lemma s f comm

@[to_additive]
lemma noncommProd_induction (s : Finset α) (f : α → β) (comm)
    (p : β → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p (f x)) :
    p (s.noncommProd f comm) := by
  refine Multiset.noncommProd_induction _ _ _ hom unit fun b hb ↦ ?_
  obtain (⟨a, ha : a ∈ s, rfl : f a = b⟩) := by simpa using hb
  exact base a ha

@[to_additive (attr := congr)]
theorem noncommProd_congr {s₁ s₂ : Finset α} {f g : α → β} (h₁ : s₁ = s₂)
    (h₂ : ∀ x ∈ s₂, f x = g x) (comm) :
    noncommProd s₁ f comm =
      noncommProd s₂ g fun x hx y hy h => by
        dsimp only [Function.onFun]
        rw [← h₂ _ hx, ← h₂ _ hy]
        subst h₁
        exact comm hx hy h := by
  simp_rw [noncommProd, Multiset.map_congr (congr_arg _ h₁) h₂]

@[to_additive (attr := simp)]
theorem noncommProd_toFinset [DecidableEq α] (l : List α) (f : α → β) (comm) (hl : l.Nodup) :
    noncommProd l.toFinset f comm = (l.map f).prod := by
  rw [← List.dedup_eq_self] at hl
  simp [noncommProd, hl]

@[to_additive (attr := simp)]
theorem noncommProd_empty (f : α → β) (h) : noncommProd (∅ : Finset α) f h = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem noncommProd_cons (s : Finset α) (a : α) (f : α → β)
    (ha : a ∉ s) (comm) :
    noncommProd (cons a s ha) f comm =
      f a * noncommProd s f (comm.mono fun _ => Finset.mem_cons.2 ∘ .inr) := by
  simp_rw [noncommProd, Finset.cons_val, Multiset.map_cons, Multiset.noncommProd_cons]

@[to_additive]
theorem noncommProd_cons' (s : Finset α) (a : α) (f : α → β)
    (ha : a ∉ s) (comm) :
    noncommProd (cons a s ha) f comm =
      noncommProd s f (comm.mono fun _ => Finset.mem_cons.2 ∘ .inr) * f a := by
  simp_rw [noncommProd, Finset.cons_val, Multiset.map_cons, Multiset.noncommProd_cons']

@[to_additive (attr := simp)]
theorem noncommProd_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      f a * noncommProd s f (comm.mono fun _ => mem_insert_of_mem) := by
  simp only [← cons_eq_insert _ _ ha, noncommProd_cons]

@[to_additive]
theorem noncommProd_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      noncommProd s f (comm.mono fun _ => mem_insert_of_mem) * f a := by
  simp only [← cons_eq_insert _ _ ha, noncommProd_cons']

@[to_additive (attr := simp)]
theorem noncommProd_singleton (a : α) (f : α → β) :
    noncommProd ({a} : Finset α) f
        (by
          norm_cast
          exact Set.pairwise_singleton _ _) =
      f a := mul_one _

variable [FunLike F β γ]

@[to_additive]
theorem map_noncommProd [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (comm) (g : F) :
    g (s.noncommProd f comm) =
      s.noncommProd (fun i => g (f i)) fun _ hx _ hy _ => (comm.of_refl hx hy).map g := by
  simp [noncommProd, Multiset.map_noncommProd]

@[deprecated (since := "2024-07-23")] alias noncommProd_map := map_noncommProd
@[deprecated (since := "2024-07-23")] alias noncommSum_map := map_noncommSum

@[to_additive noncommSum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Finset α) (f : α → β) (comm) (m : β) (h : ∀ x ∈ s, f x = m) :
    s.noncommProd f comm = m ^ s.card := by
  rw [noncommProd, Multiset.noncommProd_eq_pow_card _ _ m]
  · simp only [Finset.card_def, Multiset.card_map]
  · simpa using h

@[to_additive]
theorem noncommProd_commute (s : Finset α) (f : α → β) (comm) (y : β)
    (h : ∀ x ∈ s, Commute y (f x)) : Commute y (s.noncommProd f comm) := by
  apply Multiset.noncommProd_commute
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

theorem mul_noncommProd_erase [DecidableEq α] (s : Finset α) {a : α} (h : a ∈ s) (f : α → β) (comm)
    (comm' := fun _ hx _ hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    f a * (s.erase a).noncommProd f comm' = s.noncommProd f comm := by
  classical
  simpa only [← Multiset.map_erase_of_mem _ _ h] using
    Multiset.mul_noncommProd_erase (s.1.map f) (Multiset.mem_map_of_mem f h) _

theorem noncommProd_erase_mul [DecidableEq α] (s : Finset α) {a : α} (h : a ∈ s) (f : α → β) (comm)
    (comm' := fun _ hx _ hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    (s.erase a).noncommProd f comm' * f a = s.noncommProd f comm := by
  classical
  simpa only [← Multiset.map_erase_of_mem _ _ h] using
    Multiset.noncommProd_erase_mul (s.1.map f) (Multiset.mem_map_of_mem f h) _

@[to_additive]
theorem noncommProd_eq_prod {β : Type*} [CommMonoid β] (s : Finset α) (f : α → β) :
    (noncommProd s f fun _ _ _ _ _ => Commute.all _ _) = s.prod f := by
  induction' s using Finset.cons_induction_on with a s ha IH
  · simp
  · simp [ha, IH]

/-- The non-commutative version of `Finset.prod_union` -/
@[to_additive "The non-commutative version of `Finset.sum_union`"]
theorem noncommProd_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t)
    (f : α → β) (comm : { x | x ∈ s ∪ t }.Pairwise (Commute on f)) :
    noncommProd (s ∪ t) f comm =
      noncommProd s f (comm.mono <| coe_subset.2 subset_union_left) *
        noncommProd t f (comm.mono <| coe_subset.2 subset_union_right) := by
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t
  rw [List.disjoint_toFinset_iff_disjoint] at h
  calc noncommProd (List.toFinset sl ∪ List.toFinset tl) f comm
     = noncommProd ⟨↑(sl ++ tl), Multiset.coe_nodup.2 (sl'.append tl' h)⟩ f
         (by convert comm; simp [Set.ext_iff]) := noncommProd_congr (by ext; simp) (by simp) _
   _ = noncommProd (List.toFinset sl) f (comm.mono <| coe_subset.2 subset_union_left) *
         noncommProd (List.toFinset tl) f (comm.mono <| coe_subset.2 subset_union_right) := by
    simp [noncommProd, List.dedup_eq_self.2 sl', List.dedup_eq_self.2 tl', h]

@[to_additive]
theorem noncommProd_mul_distrib_aux {s : Finset α} {f : α → β} {g : α → β}
    (comm_ff : (s : Set α).Pairwise (Commute on f))
    (comm_gg : (s : Set α).Pairwise (Commute on g))
    (comm_gf : (s : Set α).Pairwise fun x y => Commute (g x) (f y)) :
    (s : Set α).Pairwise fun x y => Commute ((f * g) x) ((f * g) y) := by
  intro x hx y hy h
  apply Commute.mul_left <;> apply Commute.mul_right
  · exact comm_ff.of_refl hx hy
  · exact (comm_gf hy hx h.symm).symm
  · exact comm_gf hx hy h
  · exact comm_gg.of_refl hx hy

/-- The non-commutative version of `Finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `Finset.sum_add_distrib`"]
theorem noncommProd_mul_distrib {s : Finset α} (f : α → β) (g : α → β) (comm_ff comm_gg comm_gf) :
    noncommProd s (f * g) (noncommProd_mul_distrib_aux comm_ff comm_gg comm_gf) =
      noncommProd s f comm_ff * noncommProd s g comm_gg := by
  induction' s using Finset.cons_induction_on with x s hnmem ih
  · simp
  rw [Finset.noncommProd_cons, Finset.noncommProd_cons, Finset.noncommProd_cons, Pi.mul_apply,
    ih (comm_ff.mono fun _ => mem_cons_of_mem) (comm_gg.mono fun _ => mem_cons_of_mem)
      (comm_gf.mono fun _ => mem_cons_of_mem),
    (noncommProd_commute _ _ _ _ fun y hy => ?_).mul_mul_mul_comm]
  exact comm_gf (mem_cons_self x s) (mem_cons_of_mem hy) (ne_of_mem_of_not_mem hy hnmem).symm

section FinitePi

variable {M : ι → Type*} [∀ i, Monoid (M i)]

@[to_additive]
theorem noncommProd_mul_single [Fintype ι] [DecidableEq ι] (x : ∀ i, M i) :
    (univ.noncommProd (fun i => Pi.mulSingle i (x i)) fun i _ j _ _ =>
        Pi.mulSingle_apply_commute x i j) = x := by
  ext i
  apply (univ.map_noncommProd (fun i ↦ MonoidHom.mulSingle M i (x i)) ?a
    (Pi.evalMonoidHom M i)).trans
  case a =>
    intro i _ j _ _
    exact Pi.mulSingle_apply_commute x i j
  convert (noncommProd_congr (insert_erase (mem_univ i)).symm _ _).trans _
  · intro j
    exact Pi.mulSingle j (x j) i
  · intro j _; dsimp
  · rw [noncommProd_insert_of_not_mem _ _ _ _ (not_mem_erase _ _),
      noncommProd_eq_pow_card (univ.erase i), one_pow, mul_one]
    · simp only [MonoidHom.mulSingle_apply, ne_eq, Pi.mulSingle_eq_same]
    · intro j hj
      simp? at hj says simp only [mem_erase, ne_eq, mem_univ, and_true] at hj
      simp only [MonoidHom.mulSingle_apply, Pi.mulSingle, Function.update, Eq.ndrec, Pi.one_apply,
        ne_eq, dite_eq_right_iff]
      intro h
      simp [*] at *

@[to_additive]
theorem _root_.MonoidHom.pi_ext [Finite ι] [DecidableEq ι] {f g : (∀ i, M i) →* γ}
    (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g := by
  cases nonempty_fintype ι
  ext x
  rw [← noncommProd_mul_single x, univ.map_noncommProd, univ.map_noncommProd]
  congr 1 with i; exact h i (x i)

end FinitePi

end Finset
