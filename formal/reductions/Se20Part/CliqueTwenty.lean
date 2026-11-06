import Se20Part.Legacy.Bounds.TwentyCliqueRigidity
import Se20Part.LegacyBridge
import Se20Part.Critical
import Se20Part.CompactGeometry

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- G02's ambient strong-clique bound. -/
theorem strong_clique_twenty (hΔ : MaxDegreeFour G) (Q : Finset G.edgeSet)
    (hQ : (L2 G).IsClique (Q : Set G.edgeSet)) : Q.card ≤ 20 := by
  apply Legacy.clique_card_le_twenty G hΔ Q
  rwa [legacy_conflictGraph_eq G]

theorem twenty_clique_closed (hΔ : MaxDegreeFour G) (Q : Finset G.edgeSet)
    (hQ : (L2 G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20)
    {e f : G.edgeSet} (he : e ∈ Q) (hef : (L2 G).Adj e f) : f ∈ Q := by
  apply Legacy.twenty_clique_conflict_closed G hΔ Q (by rwa [legacy_conflictGraph_eq G]) hq he
  rwa [legacy_conflictGraph_eq G]

/-- The equality case includes five disjoint pairs with exact ambient
neighbour sets. Thus witnesses and edges outside the selected set cannot be
discarded. This is the concrete whole-component version of C₅[2]. -/
theorem twenty_clique_rigidity (hΔ : MaxDegreeFour G) (Q : Finset G.edgeSet)
    (hQ : (L2 G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20) :
    Legacy.IsFiveCycleBlowupComponent G (edgeSupport G Q) := by
  have heq : Legacy.selectedSupport G Q = edgeSupport G Q := by
    ext v
    constructor
    · intro hv
      obtain ⟨e,he⟩ := Finset.card_pos.mp (Finset.mem_filter.mp hv).2
      obtain ⟨heQ,hve⟩ := Finset.mem_filter.mp he
      exact Finset.mem_biUnion.mpr ⟨e,heQ,Sym2.mem_toFinset.mpr hve⟩
    · intro hv
      obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.card_pos.mpr
        ⟨e,Finset.mem_filter.mpr ⟨he,Sym2.mem_toFinset.mp hve⟩⟩⟩
  rw [← heq]
  exact Legacy.twenty_clique_support_is_five_cycle_blowup G hΔ Q
    (by rwa [legacy_conflictGraph_eq G]) hq

/-- A finite set of at most k vertices admits a k-colouring regardless of
its edges. -/
theorem colourable_of_finset_card {W : Type*} (H : SimpleGraph W) (F : Finset W)
    (k : ℕ) (hF : F.card ≤ k) : (H.induce (F : Set W)).Colorable k := by
  let f : F ↪ Fin k := (Fintype.equivFin F).toEmbedding.trans
    (Fin.castLEEmb (by simpa using hF))
  exact ⟨SimpleGraph.Coloring.mk f (fun {_ _} h he => h.ne (f.injective he))⟩

/-- A 21-critical edge set cannot contain a 20-clique: the whole closed
clique can be coloured independently of its complement. -/
theorem critical21_clique_nineteen (hΔ : MaxDegreeFour G)
    {F : Finset G.edgeSet} (hF : Critical21 G F)
    (Q : Finset G.edgeSet) (hQF : Q ⊆ F)
    (hQ : (L2 G).IsClique (Q : Set G.edgeSet)) : Q.card ≤ 19 := by
  have h20 := strong_clique_twenty G hΔ Q hQ
  by_contra hn
  have hq : Q.card = 20 := by omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
  obtain ⟨φ⟩ := (partialColouring_iff_colourable (L2 G) (F.erase e)).mpr (hF.2.2 e (hQF he))
  obtain ⟨ψ⟩ := (partialColouring_iff_colourable (L2 G) Q).mpr
    (colourable_of_finset_card (L2 G) Q 20 h20)
  apply hF.2.1
  apply (partialColouring_iff_colourable (L2 G) F).mp
  refine ⟨⟨fun x => if x ∈ Q then ψ.colour x else φ.colour x,?_⟩⟩
  intro x y hx hy hxy
  by_cases hxQ : x ∈ Q
  · have hyQ := twenty_clique_closed G hΔ Q hQ hq hxQ hxy
    simpa only [if_pos hxQ,if_pos hyQ] using ψ.proper hxQ hyQ hxy
  · have hyQ : y ∉ Q := fun hyQ => hxQ (twenty_clique_closed G hΔ Q hQ hq hyQ hxy.symm)
    have hxe : x ≠ e := fun hh => hxQ (hh.symm ▸ he)
    have hye : y ≠ e := fun hh => hyQ (hh.symm ▸ he)
    simpa only [if_neg hxQ,if_neg hyQ] using
      φ.proper (Finset.mem_erase.mpr ⟨hxe,hx⟩) (Finset.mem_erase.mpr ⟨hye,hy⟩) hxy

end Se20Part
