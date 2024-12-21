import Mathlib.Combinatorics.SimpleGraph.Finite
namespace Finset
variable {α : Type*} [DecidableEq α]
/-- Useful trivial fact about when |{a,b,c,d}| ≤ 2 given a ≠ b , a ≠ d, b ≠ c  -/
lemma card_le_two_of_four {a b c d : α} (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c)
(hc2: card {a,b,c,d} ≤ 2): c = a ∧ d = b:=by
  by_contra! hf
  apply (card {a, b, c, d}).le_lt_asymm hc2 <| two_lt_card_iff.2 _
  by_cases hac: a = c <;> simp only [mem_insert,mem_singleton]
  · exact ⟨a,b,d,Or.inl rfl, Or.inr <| Or.inl rfl,Or.inr <| Or.inr <| Or.inr rfl,hab,had,
      fun hbd => (hf hac.symm) hbd.symm⟩
  · exact ⟨a,b,c,Or.inl rfl,Or.inr <| Or.inl rfl,Or.inr <| Or.inr <| Or.inl rfl,hab,hac,hbc⟩


lemma insert_inter_insert {a : α}{s t : Finset α} : insert a s ∩ insert a t = insert a (s ∩ t):=by
  ext x; simp only [mem_inter, mem_insert]
  constructor <;> tauto

end Finset

namespace SimpleGraph
section degree
variable {α : Type*} {G H : SimpleGraph α}


variable {x : α} [Fintype (H.neighborSet x)]

/-- If G is a subgraph of H then d_G(x) ≤ d_H(x) for any vertex x -/
lemma degree_le  (hle : G ≤ H) [Fintype (G.neighborSet x)] :
    G.degree x ≤ H.degree x:= by
  simp only [← card_neighborSet_eq_degree]
  apply Set.card_le_card fun v hv  => by exact hle hv

variable [Fintype α]
variable [DecidableRel G.Adj] [DecidableRel H.Adj]
/-- If there are no vertices then the minDegree is zero -/
@[simp]
lemma minDegree_eq_zero [IsEmpty α] : G.minDegree = 0:= by
  rw [minDegree,WithTop.untop'_eq_self_iff]
  right
  simp

/--If G is a subgraph of H then δ(G) ≤ δ(H) -/
lemma minDegree_le_minDegree (hle : G ≤ H) : G.minDegree  ≤ H.minDegree := by
  by_cases hne : Nonempty α
  · apply le_minDegree_of_forall_le_degree;
    intro v; apply (G.minDegree_le_degree v).trans (G.degree_le hle)
  · rw [not_nonempty_iff] at hne
    simp

/--If G is a subgraph of H then Δ(G) ≤ Δ(H) -/
lemma maxDegree_le_maxDegree (hle : G ≤ H) : G.maxDegree  ≤ H.maxDegree := by
  apply maxDegree_le_of_forall_degree_le
  intro v
  apply (degree_le hle).trans <| degree_le_maxDegree H v

end degree
section finedges
variable {α : Type*} {G H : SimpleGraph α}
def edgeSetOfLEfintype {G H : SimpleGraph α} [Fintype G.edgeSet] [DecidableRel G.Adj]
[DecidableRel H.Adj](hle : H ≤ G) :
  Fintype H.edgeSet:= by
  apply Set.fintypeSubset G.edgeSet
  simpa using hle

/-- If `P G` holds and `G` has finitely many edges then there exists an edge minimal
subgraph H of G for which `P H` holds. -/
lemma exists_edge_minimal (P : SimpleGraph α → Prop) (hG : P G) [Fintype G.edgeSet] :
    ∃ H, H ≤ G ∧ P H  ∧ ∀ {K}, K < H → ¬ P K :=by
  let p : ℕ → Prop := fun n => ∃ H, ∃ _ : Fintype (H.edgeSet), H ≤ G ∧ P H ∧ H.edgeFinset.card ≤ n
  have h : p G.edgeFinset.card := by
    use G, inferInstance
  classical
  obtain ⟨H,_,hH⟩:=Nat.find_spec ⟨_,h⟩
  use H, hH.1,hH.2.1
  intro K hK
  have := edgeSetOfLEfintype hK.le
  have hKc: K.edgeFinset.card < H.edgeFinset.card :=
    (Finset.card_lt_card <| edgeFinset_ssubset_edgeFinset.2 hK)
  have := Nat.find_min ⟨_,h⟩ (lt_of_lt_of_le hKc hH.2.2)
  dsimp [p ] at this
  push_neg at this
  intro hF
  apply Nat.lt_irrefl K.edgeFinset.card
  convert this K (edgeSetOfLEfintype hK.le) (lt_of_lt_of_le hK hH.1).le hF

variable [Fintype α]
/--If α is finite and `P G` holds then there exists a maximal supergraph H of G
for which `P H` holds. -/
lemma exists_edge_maximal (P : SimpleGraph α → Prop) (hG : P G) :
    ∃ H, G ≤ H ∧ P H  ∧ ∀ {K}, H < K → ¬ P K :=by
  classical
  revert hG
  apply WellFounded.recursion (measure fun H  => Hᶜ.edgeFinset.card).wf G
  intro c hc _
  by_cases hm: ∀ d, c < d → ¬P d
  · use c
  · push_neg at hm
    obtain ⟨d,hd1,hd2⟩:=hm
    obtain ⟨e,hle,he⟩:= hc d ((fun h => Finset.card_lt_card <| edgeFinset_ssubset_edgeFinset.2
        <| compl_lt_compl_iff_lt.2 h) hd1) hd2
    use e, hd1.le.trans hle
end finedges
end SimpleGraph
