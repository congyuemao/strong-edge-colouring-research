import Se20Part.PaletteExtension
import Se20Part.ConflictBounds

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
local instance externalStarsDecEq : DecidableEq G.edgeSet := Classical.decEq _

def colouredStar {A : Finset G.edgeSet} (φ : PartialColouring (L2 G) A)
    (v : V) : Finset Colour := (incident G v ∩ A).image φ.colour

/-- Adjacent original vertices share at most one colour in their coloured
stars: a shared colour must belong to their unique connecting edge. -/
theorem adjacent_colouredStars_inter_le_one {A : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) A) {u v : V} (huv : G.Adj u v) :
    (colouredStar φ u ∩ colouredStar φ v).card ≤ 1 := by
  let g : G.edgeSet := ⟨s(u,v),G.mem_edgeSet.mpr huv⟩
  have hs : colouredStar φ u ∩ colouredStar φ v ⊆ {φ.colour g} := by
    intro c hc
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hc).1
    obtain ⟨f,hf,hfc⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hc).2
    have hue := (mem_incident G _ _).mp (Finset.mem_inter.mp he).1
    have hvf := (mem_incident G _ _).mp (Finset.mem_inter.mp hf).1
    have hef : e = f := by
      by_contra hn
      exact φ.proper (Finset.mem_inter.mp he).2 (Finset.mem_inter.mp hf).2
        ⟨hn,u,hue,v,hvf,Or.inr huv⟩ (hec.trans hfc.symm)
    have heg : e = g := Subtype.ext ((Sym2.mem_and_mem_iff huv.ne).mp
      ⟨hue,hef.symm ▸ hvf⟩)
    simpa only [Finset.mem_singleton,← heg] using hec.symm
  exact (Finset.card_le_card hs).trans_eq (Finset.card_singleton _)

/-- The equal-star failure state in G13 forces the corresponding external
endpoints to be nonadjacent, without an ambient girth assumption. -/
theorem equal_colouredStars_nonadjacent {A : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) A) {u v : V}
    (he : colouredStar φ u = colouredStar φ v)
    (hc : 2 ≤ (colouredStar φ u).card) : ¬ G.Adj u v := by
  intro huv
  have h := adjacent_colouredStars_inter_le_one φ huv
  rw [← he,Finset.inter_self] at h
  omega

end Se20Part
