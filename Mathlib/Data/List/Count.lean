/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.BigOperators.Basic

#align_import data.list.count from "leanprover-community/mathlib"@"47adfab39a11a072db552f47594bf8ed2cf8a722"

/-!
# Counting in lists

This file proves basic properties of `List.countp` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Std.Data.List.Basic`.
-/

set_option autoImplicit true


open Nat

variable {l : List α}

namespace List

section Countp

variable (p q : α → Bool)

#align list.countp_nil List.countp_nil

#align list.countp_cons_of_pos List.countp_cons_of_pos

#align list.countp_cons_of_neg List.countp_cons_of_neg

#align list.countp_cons List.countp_cons

#align list.length_eq_countp_add_countp List.length_eq_countp_add_countp

#align list.countp_eq_length_filter List.countp_eq_length_filter

#align list.countp_le_length List.countp_le_length

#align list.countp_append List.countp_append

theorem countp_join : ∀ l : List (List α), countp p l.join = (l.map (countp p)).sum
  | [] => rfl
  | a :: l => by rw [join, countp_append, map_cons, sum_cons, countp_join l]
#align list.countp_join List.countp_join

#align list.countp_pos List.countp_pos

#align list.countp_eq_zero List.countp_eq_zero

#align list.countp_eq_length List.countp_eq_length

theorem length_filter_lt_length_iff_exists (l) :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  simpa [length_eq_countp_add_countp p l, countp_eq_length_filter] using
  countp_pos (fun x => ¬p x) (l := l)
#align list.length_filter_lt_length_iff_exists List.length_filter_lt_length_iff_exists

#align list.sublist.countp_le List.Sublist.countp_le

#align list.countp_filter List.countp_filter

#align list.countp_true List.countp_true

#align list.countp_false List.countp_false

#align list.countp_map List.countp_map

#align list.countp_mono_left List.countp_mono_left

#align list.countp_congr List.countp_congr

end Countp

/-! ### count -/

section Count

variable [DecidableEq α]

#align list.count_nil List.count_nil

@[deprecated] theorem count_cons' (a b : α) (l : List α) :
    count a (b :: l) = count a l + if a = b then 1 else 0 := by conv =>
  simp [count, countp_cons]
  lhs
  simp only [eq_comm]
#align list.count_cons' List.count_cons'

#align list.count_cons List.count_cons

#align list.count_cons_self List.count_cons_self

#align list.count_cons_of_ne List.count_cons_of_ne

#align list.count_tail List.count_tail

#align list.count_le_length List.count_le_length

#align list.sublist.count_le List.Sublist.count_le

#align list.count_le_count_cons List.count_le_count_cons

#align list.count_singleton List.count_singleton

#align list.count_singleton' List.count_singleton'

#align list.count_append List.count_append

theorem count_join (l : List (List α)) (a : α) : l.join.count a = (l.map (count a)).sum :=
  countp_join _ _
#align list.count_join List.count_join

#align list.count_concat List.count_concat

#align list.count_pos List.count_pos_iff_mem

#align list.one_le_count_iff_mem List.count_pos_iff_mem

#align list.count_eq_zero_of_not_mem List.count_eq_zero_of_not_mem

#align list.not_mem_of_count_eq_zero List.not_mem_of_count_eq_zero

#align list.count_eq_zero List.count_eq_zero

#align list.count_eq_length List.count_eq_length

#align list.count_replicate_self List.count_replicate_self

#align list.count_replicate List.count_replicate

#align list.filter_eq' List.filter_eq'

#align list.filter_eq List.filter_eq

#align list.le_count_iff_replicate_sublist List.le_count_iff_replicate_sublist

#align list.replicate_count_eq_of_count_eq_length List.replicate_count_eq_of_count_eq_length

#align list.count_filter List.count_filter

theorem count_bind {α β} [DecidableEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.bind f) = sum (map (count x ∘ f) l) := by rw [List.bind, count_join, map_map]
#align list.count_bind List.count_bind

@[simp]
theorem count_map_of_injective {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countp_map, (· ∘ ·), hf.beq_eq]
#align list.count_map_of_injective List.count_map_of_injective

#align list.count_le_count_map List.count_le_count_map

#align list.count_erase List.count_erase

#align list.count_erase_self List.count_erase_self

#align list.count_erase_of_ne List.count_erase_of_ne

@[to_additive]
theorem prod_map_eq_pow_single [Monoid β] (a : α) (f : α → β)
    (hf : ∀ a', a' ≠ a → a' ∈ l → f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction' l with a' as h generalizing a
  · rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  · specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ]
    · rw [hf a' (Ne.symm ha') (List.mem_cons_self a' as), one_mul, add_zero]
#align list.prod_map_eq_pow_single List.prod_map_eq_pow_single
#align list.sum_map_eq_nsmul_single List.sum_map_eq_nsmul_single

@[to_additive]
theorem prod_eq_pow_single [Monoid α] (a : α)
    (h : ∀ a', a' ≠ a → a' ∈ l → a' = 1) : l.prod = a ^ l.count a :=
  _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)
#align list.prod_eq_pow_single List.prod_eq_pow_single
#align list.sum_eq_nsmul_single List.sum_eq_nsmul_single

end Count

end List
