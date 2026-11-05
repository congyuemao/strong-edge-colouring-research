import Se20Insertion.FanLemma

noncomputable section
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Se20Insertion.PartialColouring
variable {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}

theorem forest_tangled_direct (φ : PartialColouring (L2 G) F) (hG : G.IsAcyclic)
    {e : G.edgeSet} (he : e ∉ F) {a b : Colour} (hab : a ≠ b)
    (ht : φ.TangledAt e a b) : φ.DirectAt e a b := by
  by_contra hn
  obtain ⟨x,y,p,hx,hy,hp⟩ := φ.tangledAt_shortestPath ht
  obtain ⟨z,c,hc,_,_⟩ := φ.longChain_cycle hab (fun h => he h.1) hx hy p hp hn
  exact hG c hc

/-- The structural assertion in 11.1 holds also for infinite forests. -/
theorem forest_single_separable (φ : PartialColouring (L2 G) F) (hG : G.IsAcyclic)
    {e f g : G.edgeSet} (he : e ∉ F) {a b : Colour} (hab : a ≠ b)
    (hf : φ.Single e a f) (hg : φ.Single e b g) (hfg : ¬ (L2 G).Adj f g) :
    φ.Separable e a b := by
  by_contra hn
  obtain ⟨x,y,hx,hy,hxy⟩ := φ.forest_tangled_direct hG he hab
    ((φ.tangledAt_iff_not_separable e a b).mpr hn)
  exact hfg (hf.2 x hx ▸ hg.2 y hy ▸ hxy)

/-- Finite maximum-degree-four version of Lemma 11.1; blockedness is unnecessary. -/
theorem finite_forest_separable [Fintype V] (φ : PartialColouring (L2 G) F)
    (hG : G.IsAcyclic) (hΔ : MaxDegreeFour G) {e : G.edgeSet} (he : e ∉ F) :
    ∃ a b, a ≠ b ∧ φ.Separable e a b := by
  by_contra hn
  have hd (a b : Colour) (hab : a ≠ b) : φ.DirectAt e a b :=
    φ.forest_tangled_direct hG he hab ((φ.tangledAt_iff_not_separable e a b).mpr
      (fun hs => hn ⟨a,b,hab,hs⟩))
  let S : Finset (Sym2 Colour) := Finset.univ.filter (fun c => ¬ c.IsDiag)
  have hS : S.card = 190 := by decide
  have hsub : S ⊆ φ.directPairs e := by
    intro c hc
    obtain ⟨a,b,rfl⟩ : ∃ a b, c = s(a,b) := Sym2.ind (fun a b => ⟨a,b,rfl⟩) c
    have hab : a ≠ b := by simpa [S] using hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b,rfl,hd a b hab⟩
  have hle := Finset.card_le_card hsub
  have hmax := φ.directPairs_le_87 hΔ (by rw [hG.egirth_eq_top]; exact le_top) e
  omega

end Se20Insertion.PartialColouring
