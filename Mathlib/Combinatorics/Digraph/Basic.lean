import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite

open Finset Function

universe u v w

/-- A directed graph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
-/
@[ext]
structure Digraph (V : Type u) where
  Adj : V → V → Prop


-- JACK: This might have been deprecated? check Mathlib/Tactic/ProjectionNotation.lean
--pp_extended_field_notation Digraph.Adj

noncomputable instance {V : Type u} [Fintype V] : Fintype (Digraph V) := by
  classical exact Fintype.ofInjective Digraph.Adj Digraph.ext


/-- Constructor for digraphs using a symmetric irreflexive boolean function. -/
-- Fix this for directed graphs

@[simps]
def Digraph.mk' {V : Type u} :
    (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' := by
    intro adj adj'
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w


/-- Construct the digraph induced by the given relation. -/
def Digraph.fromRel {V : Type u} (r : V → V → Prop) : Digraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)

@[simp]
theorem Digraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (Digraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def Digraph.completeGraph (V : Type u) : Digraph V where Adj _ _ := True

/-- The graph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def Digraph.emptyGraph (V : Type u) : Digraph V where Adj _ _ := False

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

namespace Digraph

variable {ι : Sort _} {𝕜 : Type _} {V : Type u} {W : Type v} {X : Type w} (G : Digraph V)
  (G' : Digraph W) {a b c u v w : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) :=
  Digraph.ext

@[simp]
theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff

section Order

/-- The relation that one `Digraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (Digraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) :=
  rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Sup (Digraph V) where
  sup x y :=
    { Adj := x.Adj ⊔ y.Adj }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Inf (Digraph V) where
  inf x y :=
    { Adj := x.Adj ⊓ y.Adj }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
instance hasCompl : HasCompl (Digraph V) where
  compl G :=
    { Adj := fun v w => ¬G.Adj v w }

@[simp]
theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s :=
    { Adj := fun a b => ∃ G ∈ s, Adj G a b }

instance infSet : InfSet (Digraph V) where
  sInf s :=
    { Adj := fun a b => (∀ ⦃G⦄, G ∈ s → Adj G a b) }

@[simp]
theorem sSup_adj {s : Set (Digraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by
  simp [iInf]

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  { show DistribLattice (Digraph V) from
      adj_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := fun G H => ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeBooleanAlgebra : CompleteBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeGraph V
    bot := emptyGraph V
    le_top := fun x v w _ => trivial
    bot_le := fun x v w h => h.elim
    sdiff_eq := fun x y => by
      ext (v w)
      exact Iff.rfl
    inf_compl_le_bot := fun G v w h => False.elim <| h.2 h.1
    top_le_sup_compl := fun G v w _ => by
      by_cases h : G.Adj v w
      · exact Or.inl h
      · exact Or.inr h
    sSup := sSup
    le_sSup := fun s G hG a b hab => ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b => by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun s G hG a b hab => hab hG
    le_sInf := fun s G hG a b hab => fun H hH => hG _ hH hab
    inf_sSup_le_iSup_inf := fun G s a b hab => by simpa using hab
    iInf_sup_le_sup_sInf := fun G s a b hab => by
      simpa [forall_and, forall_or_left, or_and_right] using hab }

@[simp]
theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp]
theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

@[simps]
instance (V : Type u) : Inhabited (Digraph V) :=
  ⟨⊥⟩

/-
-- This is false. Check if we should prove ¬ Unique instead of just getting rid of it
instance [Subsingleton V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by
    ext a b
    have := Subsingleton.elim a b
    simp [this]
-/


instance [Nontrivial V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  rw [← completeGraph_eq_top, ← emptyGraph_eq_bot, Digraph.completeGraph, Digraph.emptyGraph]
  simp only [ne_eq, mk.injEq]
  rw [@funext_iff]
  simp only [forall_const]
  rw [@funext_iff]
  simp only [eq_iff_iff, iff_true, forall_const, not_false_eq_true]

  /-
  Original proof doesn't compile in this case, I don't know how to modify it to make it work:

  ⟨⟨⊥, ⊤, fun h ↦ not_subsingleton V ⟨by simpa only [← adj_inj, Function.funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩
  -/

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => True

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

end Decidable

end Order

