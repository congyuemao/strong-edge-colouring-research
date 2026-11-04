import Se20Insertion.HoleMoves

noncomputable section
open scoped Classical
namespace Se20Insertion

/-- Lemma 11.6(2) and the sharpened length-one count in Corollary 11.8. -/
theorem single_neighbour_at_least_fifteen {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) {e f : G.edgeSet} {p : Colour}
    (he : e ∉ F) (hs : φ.Single e p f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b) :
    15 ≤ (φ.singleColours f).card := by
  let N := φ.colouredNeighbours f
  let A : Finset Colour := Finset.univ.erase p
  have hcount := φ.single_count N A (by
    intro c hc
    have hcp : c ≠ p := (Finset.mem_erase.mp hc).1
    obtain ⟨g, hg, hfg, hgc⟩ := φ.single_saturated_of_no_trivial hs hnt c hcp
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, hfg⟩, hgc⟩)
  have hA : A.card = 19 := by simp [A]
  have hN : N.card ≤ 23 := by
    have hec : e ∈ conflicts G f \ F := Finset.mem_sdiff.mpr
      ⟨(mem_conflicts G _ _).mpr hs.1.2.1.symm, he⟩
    have hpos : 0 < (conflicts G f \ F).card := Finset.card_pos.mpr ⟨e, hec⟩
    have hparts := Finset.card_sdiff_add_card_inter (conflicts G f) F
    have hmax := card_conflicts_le_twentyFour G hΔ f
    have heq : N = conflicts G f ∩ F := by
      ext g
      simp [N, PartialColouring.colouredNeighbours, and_comm]
    rw [← heq] at hparts
    omega
  have hsub : A.filter (fun c => (N.filter (φ.colour · = c)).card = 1) ⊆ φ.singleColours f := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
  have hle := Finset.card_le_card hsub
  rw [hA] at hcount
  omega

/-- The numerical part of Corollary 11.8, for any forbidden colour set `Y`.
The saturation assumption is explicit; the chain obstruction is not assumed
to imply saturation at the boundary where fewer than two colours remain. -/
theorem outside_colours_single_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) (e : G.edgeSet) (Y : Finset Colour)
    (hb : ∀ c ∉ Y, ∃ g, φ.Neighbour e c g) :
    2 * (20 - Y.card) - 24 ≤
      ((Finset.univ \ Y).filter (fun c =>
        ((φ.colouredNeighbours e).filter (φ.colour · = c)).card = 1)).card := by
  have hc := φ.single_count (φ.colouredNeighbours e) (Finset.univ \ Y) (by
    intro c hc
    obtain ⟨g, hg, heg, hgc⟩ := hb c (Finset.mem_sdiff.mp hc).2
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, heg⟩, hgc⟩)
  have hmax : (φ.colouredNeighbours e).card ≤ 24 := by
    apply (Finset.card_le_card (show φ.colouredNeighbours e ⊆ conflicts G e from ?_)).trans
      (card_conflicts_le_twentyFour G hΔ e)
    intro g hg
    exact (mem_conflicts G _ _).mpr (Finset.mem_filter.mp hg).2
  have hY : (Finset.univ \ Y).card = 20 - Y.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    rfl
  rw [hY] at hc
  omega

end Se20Insertion
