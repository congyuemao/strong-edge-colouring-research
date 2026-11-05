import Se20Insertion.InfiniteForest

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

/-- The critical-graph reduction needed before the Gallai characterization:
every nonempty induced set of degree-20 vertices has a noncolourable degree-list assignment. -/
theorem critical_low_degree_list_obstruction (hcrit : CriticalSet H F)
    (U : Finset W) (hU : U ⊆ F) (hne : U.Nonempty)
    (hdeg : ∀ x ∈ U, (F.filter (H.Adj x)).card = 20) :
    ∃ L : W → Finset Colour,
      (∀ x ∈ U, (U.filter (H.Adj x)).card ≤ (L x).card) ∧
      ¬ ∃ c : U → Colour, (∀ x, c x ∈ L x.val) ∧
        ∀ x y : U, H.Adj x.val y.val → c x ≠ c y := by
  obtain ⟨e,he⟩ := hne
  obtain ⟨φ₀⟩ := hcrit.2 e (hU he)
  let φ := φ₀.restrict (F \ U) (by
    intro x hx; exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ he), (Finset.mem_sdiff.mp hx).1⟩)
  refine ⟨φ.available,?_,?_⟩
  · intro x hx
    have ha := φ.available_card x
    have hp := Finset.card_sdiff_add_card_inter (F.filter (H.Adj x)) U
    have hout : (F.filter (H.Adj x)) \ U = φ.colouredNeighbours x := by
      ext y; simp [PartialColouring.colouredNeighbours]; tauto
    have hin : (F.filter (H.Adj x)) ∩ U = U.filter (H.Adj x) := by
      ext y; simp only [Finset.mem_filter,Finset.mem_inter]; exact
        ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hU h.1,h.2⟩,h.1⟩⟩
    rw [hout,hin,hdeg x hx] at hp
    omega
  · rintro ⟨c,hc,hproper⟩
    apply hcrit.1
    refine ⟨⟨fun x => if hx : x ∈ U then c ⟨x,hx⟩ else φ.colour x,?_⟩⟩
    intro x y hx hy hxy heq
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · exact hproper ⟨x,hxU⟩ ⟨y,hyU⟩ hxy (by simpa [hxU,hyU] using heq)
    · exact (Finset.mem_filter.mp (hc ⟨x,hxU⟩)).2
        ⟨y,Finset.mem_sdiff.mpr ⟨hy,hyU⟩,hxy,by simpa [hxU,hyU] using heq.symm⟩
    · exact (Finset.mem_filter.mp (hc ⟨y,hyU⟩)).2
        ⟨x,Finset.mem_sdiff.mpr ⟨hx,hxU⟩,hxy.symm,by simpa [hxU,hyU] using heq⟩
    · exact φ.proper (Finset.mem_sdiff.mpr ⟨hx,hxU⟩) (Finset.mem_sdiff.mpr ⟨hy,hyU⟩) hxy
        (by simpa [hxU,hyU] using heq)

end Se20Insertion
