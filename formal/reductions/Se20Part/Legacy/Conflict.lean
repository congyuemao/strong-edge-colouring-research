module

public import Se20Part.Legacy.Basic

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*}

/-- Pairwise nonconflicting original edges, with all witnesses taken from `G`. -/
def IsInducedMatching (G : SimpleGraph V) (S : Set G.edgeSet) : Prop :=
  S.Pairwise (fun e f => ¬ StrongConflict G e f)

theorem conflictGraph_independent_iff (G : SimpleGraph V) (S : Set G.edgeSet) :
    (conflictGraph G).IsIndepSet S ↔ IsInducedMatching G S := Iff.rfl

theorem candidate_independent_iff (G : SimpleGraph V) (F : Set G.edgeSet) (S : Set F) :
    (candidateConflictGraph G F).IsIndepSet S ↔
      IsInducedMatching G (Subtype.val '' S) := by
  constructor
  · intro h e he f hf hne
    rcases he with ⟨e, he, rfl⟩
    rcases hf with ⟨f, hf, rfl⟩
    exact h he hf (fun heq => hne (congrArg Subtype.val heq))
  · intro h e he f hf hne
    exact h ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩ (fun heq => hne (Subtype.ext heq))

/-- Restricting the vertex set of a conflict graph cannot increase degrees. -/
theorem induced_degree_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (F : Set W) [DecidablePred (· ∈ F)] (e : F) :
    (H.induce F).degree e ≤ H.degree e.val := by
  have hc := Finset.card_le_card
    (Finset.inter_subset_left : H.neighborFinset e.val ∩ F.toFinset ⊆ H.neighborFinset e.val)
  rw [← H.map_neighborFinset_induce e, Finset.card_map] at hc
  exact hc

theorem candidate_degree_le_full (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    [DecidableRel (conflictGraph G).Adj]
    (F : Set G.edgeSet) [DecidablePred (· ∈ F)] (e : F) :
    (candidateConflictGraph G F).degree e ≤ (conflictGraph G).degree e.val :=
  induced_degree_le (conflictGraph G) F e

end Se20Part.Legacy
