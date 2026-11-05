import Se20Part.ChordalFan
import Mathlib.Combinatorics.SimpleGraph.Girth

noncomputable section
open scoped Classical
namespace Se20Part

/-- A chordless cycle, indexed once around the cycle. Values at indices ≥ n
are unused. This has exactly the hypotheses of `forest_L2_chordal`. -/
structure InducedCycle {W : Type*} (H : SimpleGraph W) (n : ℕ) where
  vertex : ℕ → W
  three_le : 3 ≤ n
  injective : ∀ i < n, ∀ j < n, vertex i = vertex j → i = j
  step : ∀ i < n-1, H.Adj (vertex i) (vertex (i+1))
  close : H.Adj (vertex 0) (vertex (n-1))
  no_chord : ∀ i j, i+1 < j → j < n → (i ≠ 0 ∨ j ≠ n-1) →
    ¬ H.Adj (vertex i) (vertex j)

theorem exists_edge_induce {V : Type*} (G : SimpleGraph V) (S : Set V)
    (e : G.edgeSet) (he : ∀ v ∈ e.val, v ∈ S) :
    ∃ f : (G.induce S).edgeSet, (inducedEmbedding G S).mapEdgeSet f = e := by
  obtain ⟨u,v,huv⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hu := he u (huv ▸ Sym2.mem_mk_left u v)
  have hv := he v (huv ▸ Sym2.mem_mk_right u v)
  refine ⟨⟨s(⟨u,hu⟩,⟨v,hv⟩), ?_⟩, ?_⟩
  · exact G.mem_edgeSet.mp (huv ▸ e.prop)
  · apply Subtype.ext
    exact huv.symm

/-- The exact integer formulation of Lemma 4.5: g ≤ 2ℓ.
No maximum-degree assumption and no Cameron hypothesis are used. -/
theorem induced_cycle_length_bound {V : Type*} (G : SimpleGraph V)
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (C : InducedCycle (L2 G) n)
    (hn : 4 ≤ n) : g ≤ 2 * n := by
  let S : Finset V := (Finset.range n).biUnion (fun i => (C.vertex i).val.toFinset)
  have hS : S.card ≤ 2*n := by
    calc
      S.card ≤ ∑ i ∈ Finset.range n, (C.vertex i).val.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Finset.range n, 2 := Finset.sum_le_sum (by
        intro i _
        rw [Sym2.card_toFinset]
        split_ifs <;> omega)
      _ = 2*n := by simp [Nat.mul_comm]
  have liftable (i : Fin n) : ∃ f : (G.induce (S : Set V)).edgeSet,
      (inducedEmbedding G S).mapEdgeSet f = C.vertex i := by
    apply exists_edge_induce
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr i.isLt, Sym2.mem_toFinset.mpr hv⟩
  choose q hq using liftable
  let p : ℕ → (G.induce (S : Set V)).edgeSet := fun i => q ⟨i % n, Nat.mod_lt _ (by omega)⟩
  have hp (i : ℕ) (hi : i < n) :
      (inducedEmbedding G S).mapEdgeSet (p i) = C.vertex i := by
    simpa only [p, Nat.mod_eq_of_lt hi] using hq ⟨i % n, Nat.mod_lt _ (by omega)⟩
  have hnot : ¬ (G.induce (S : Set V)).IsAcyclic := by
    intro ha
    have ht := forest_L2_chordal ha C.three_le p
      (fun i hi j hj he => C.injective i hi j hj (by
        rw [← hp i hi, ← hp j hj, he]))
      (fun i hi => (L2_induce_adj_iff G S _ _).mp (by
        rw [hp i (by omega), hp (i+1) (by omega)]; exact C.step i hi))
      ((L2_induce_adj_iff G S _ _).mp (by
        rw [hp 0 (by omega), hp (n-1) (by omega)]; exact C.close))
      (fun i j hij hj hc hadj => C.no_chord i j hij hj hc (by
        have h := (L2_induce_adj_iff G S _ _).mpr hadj
        rwa [hp i (by omega), hp j hj] at h))
    omega
  obtain ⟨v,w,hw,_⟩ := SimpleGraph.exists_girth_eq_length.mpr hnot
  have hc : w.length ≤ S.card := by
    have hpath := hw.isPath_tail.length_lt
    have hlen := SimpleGraph.Walk.length_tail_add_one hw.not_nil
    have hcard : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
    rw [hcard] at hpath
    omega
  have hcycle := hw.map (f := (inducedEmbedding G S).toHom) (inducedEmbedding G S).injective
  have hb := hg.trans hcycle.egirth_le_length
  simp only [SimpleGraph.Walk.length_map, ENat.natCast_le_natCast] at hb
  exact hb.trans (hc.trans hS)

end Se20Part
