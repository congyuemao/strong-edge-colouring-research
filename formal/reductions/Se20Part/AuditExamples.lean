import Se20Part.Partitions

noncomputable section
open scoped Classical
namespace Se20Part

theorem L2_complete {V : Type*} : L2 (⊤ : SimpleGraph V) = ⊤ := by
  ext e f
  change (_ ∧ _) ↔ e ≠ f
  constructor
  · exact And.left
  · intro hne
    obtain ⟨a,b,he⟩ : ∃ a b, e.val = s(a,b) := Sym2.ind (fun a b => ⟨a,b,rfl⟩) e.val
    obtain ⟨c,d,hf⟩ : ∃ c d, f.val = s(c,d) := Sym2.ind (fun c d => ⟨c,d,rfl⟩) f.val
    refine ⟨hne,a,he ▸ Sym2.mem_mk_left a b,c,hf ▸ Sym2.mem_mk_left c d,?_⟩
    by_cases hac : a = c
    · exact Or.inl hac
    · exact Or.inr hac

/-- Counterexample to the unqualified 24-regularity assertion in ROUTE_Q §1. -/
theorem complete_five_conflict_degree (e : (⊤ : SimpleGraph (Fin 5)).edgeSet) :
    FourRegular (⊤ : SimpleGraph (Fin 5)) ∧
    (L2 (⊤ : SimpleGraph (Fin 5))).degree e = 9 := by
  constructor
  · intro v
    have h := SimpleGraph.complete_graph_degree (V := Fin 5) v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at h ⊢
    simpa only [Nat.card_fin] using h
  · rw [L2_complete]
    have hcard : Fintype.card (⊤ : SimpleGraph (Fin 5)).edgeSet = 10 := by
      rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      decide
    have h := SimpleGraph.complete_graph_degree e
    rw [hcard] at h
    simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at h ⊢
    exact h

/-- The constant-one potential on a single isolated vertex is one, whereas
the expression printed in ROUTE_Q §6.2 is zero. -/
theorem degree_potential_isolate_counterexample :
    (∑ _x : Fin 1, (1 : ℤ)) ≠ 1 * 0 + (2 * 1 - 1) * 0 := by norm_num

end Se20Part
