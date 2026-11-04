import Se20Insertion.VertexDeletion

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)

/-- Delete `v` and add the matching in the complement of its neighbour graph. -/
def suppress (M : ((G.induce (G.neighborSet v))ᶜ).Subgraph) :
    SimpleGraph {x : V // x ≠ v} where
  Adj x y := G.Adj x.val y.val ∨
    ∃ hx : G.Adj v x.val, ∃ hy : G.Adj v y.val, M.Adj ⟨x.val, hx⟩ ⟨y.val, hy⟩
  symm := ⟨by
    rintro x y (h | ⟨hx, hy, h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨hy, hx, h.symm⟩⟩
  loopless := ⟨by
    rintro x (h | ⟨hx, hx', h⟩)
    · exact G.loopless.irrefl x.val h
    · exact (M.adj_sub h).1 rfl⟩

theorem induce_le_suppress (M : ((G.induce (G.neighborSet v))ᶜ).Subgraph) :
    G.induce {x | x ≠ v} ≤ suppress G v M := fun _ _ h => Or.inl h

theorem suppress_degree (M : ((G.induce (G.neighborSet v))ᶜ).Subgraph)
    (hM : M.IsPerfectMatching) (x : {x : V // x ≠ v}) :
    (suppress G v M).degree x = G.degree x.val := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  apply Equiv.symm
  by_cases hvx : G.Adj v x.val
  · have hm' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM ⟨x.val, hvx⟩
    let m := hm'.choose
    have hm := hm'.choose_spec.1
    have huniq := hm'.choose_spec.2
    have hmx : ¬ G.Adj x.val m.val := (M.adj_sub hm).2
    have hmv : m.val ≠ v := m.2.ne.symm
    let f : G.neighborSet x.val → (suppress G v M).neighborSet x := fun t =>
      if ht : t.val = v then
        ⟨⟨m.val, hmv⟩, Or.inr ⟨hvx, m.2, hm⟩⟩
      else ⟨⟨t.val, ht⟩, Or.inl t.2⟩
    apply Equiv.ofBijective f
    constructor
    · intro a b hab
      have heq := congrArg (fun z : (suppress G v M).neighborSet x => z.val.val) hab
      by_cases ha : a.val = v <;> by_cases hb : b.val = v
      · exact Subtype.ext (ha.trans hb.symm)
      · have hmb : m.val = b.val := by simpa [f, ha, hb] using heq
        exact False.elim (hmx (hmb.symm ▸ b.2))
      · have ham : a.val = m.val := by simpa [f, ha, hb] using heq
        exact False.elim (hmx (ham ▸ a.2))
      · exact Subtype.ext (by simpa [f, ha, hb] using heq)
    · intro z
      rcases z.2 with hz | ⟨hx, hz, hxz⟩
      · refine ⟨⟨z.val.val, hz⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simp [f, z.val.2]
      · have hzm : (⟨z.val.val, hz⟩ : G.neighborSet v) = m := huniq _ hxz
        refine ⟨⟨v, hvx.symm⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simpa [f] using (congrArg Subtype.val hzm).symm
  · let f : G.neighborSet x.val → (suppress G v M).neighborSet x := fun t =>
      ⟨⟨t.val, fun h => hvx (by simpa only [h] using t.2.symm)⟩, Or.inl t.2⟩
    apply Equiv.ofBijective f
    constructor
    · intro a b hab
      exact Subtype.ext (congrArg (fun z : (suppress G v M).neighborSet x => z.val.val) hab)
    · intro z
      rcases z.2 with hz | ⟨hx, _⟩
      · exact ⟨⟨z.val.val, hz⟩, rfl⟩
      · exact False.elim (hvx hx)

theorem suppress_regular (hreg : FourRegular G)
    (M : ((G.induce (G.neighborSet v))ᶜ).Subgraph) (hM : M.IsPerfectMatching) :
    FourRegular (suppress G v M) := by
  intro x
  have hd := suppress_degree G v M hM x
  have hr := hreg x.val
  simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd hr ⊢
  exact hd.trans hr

end Se20Insertion
