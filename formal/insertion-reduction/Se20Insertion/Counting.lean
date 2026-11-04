import Se20Insertion.Fragmentation
import Se20Insertion.ConflictBounds

noncomputable section
open scoped Classical
namespace Se20Insertion

/-- Equality in the finite union bound forces disjointness. -/
theorem disjoint_of_card_biUnion_eq_sum {I X : Type*} [DecidableEq X]
    (s : Finset I) (t : I → Finset X)
    (heq : (s.biUnion t).card = ∑ i ∈ s, (t i).card) :
    (s : Set I).PairwiseDisjoint t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha] at heq
    have hle : (s.biUnion t).card ≤ ∑ i ∈ s, (t i).card := Finset.card_biUnion_le
    have hcu := Finset.card_union_add_card_inter (t a) (s.biUnion t)
    have hinter : (t a ∩ s.biUnion t).card = 0 := by omega
    have hrest : (s.biUnion t).card = ∑ i ∈ s, (t i).card := by omega
    have hdisj : Disjoint (t a) (s.biUnion t) := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.card_eq_zero.mp hinter)
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with rfl | his
    · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hij.symm
      exact hdisj.mono_right (Finset.subset_biUnion_of_mem (s := s) t hjs)
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact (hdisj.mono_right (Finset.subset_biUnion_of_mem (s := s) t his)).symm
      · exact ih hrest his hjs hij

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- If at most 20 neighbours cover 20 colours, all are coloured and distinct. -/
theorem saturated_twenty (φ : PartialColouring H F) (N : Finset W) (e : W)
    (hN : ∀ x, x ∈ N ↔ H.Adj e x) (hcard : N.card ≤ 20)
    (hblocked : ∀ c, ∃ x, φ.Neighbour e c x) :
    N.card = 20 ∧ (∀ x ∈ N, x ∈ F) ∧ Set.InjOn φ.colour N := by
  let S := N.filter (· ∈ F)
  have himage : S.image φ.colour = Finset.univ := by
    ext c
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨x, hx, hex, hxc⟩ := hblocked c
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨(hN x).mpr hex, hx⟩, hxc⟩
  have hS : 20 ≤ S.card := by
    have := Finset.card_image_le (s := S) (f := φ.colour)
    simpa [himage] using this
  have hSN : S = N := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (hcard.trans hS)
  have hNcard : N.card = 20 := by rw [hSN] at hS; omega
  refine ⟨hNcard, ?_, ?_⟩
  · intro x hx
    rw [← hSN] at hx
    exact (Finset.mem_filter.mp hx).2
  · apply Finset.card_image_iff.mp
    rw [hSN] at himage
    simp [himage, hNcard]

/-- Pigeonhole count, valid for any specified set of blocked colours. -/
theorem single_count (φ : PartialColouring H F) (N : Finset W) (A : Finset Colour)
    (hblocked : ∀ c ∈ A, ∃ x ∈ N, φ.colour x = c) :
    2 * A.card ≤ N.card + (A.filter (fun c => (N.filter (φ.colour · = c)).card = 1)).card := by
  have hfib : ∑ c ∈ A, (N.filter (φ.colour · = c)).card ≤ N.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  have heach : ∀ c ∈ A,
      2 ≤ (N.filter (φ.colour · = c)).card +
        (if (N.filter (φ.colour · = c)).card = 1 then 1 else 0) := by
    intro c hc
    have hp : 0 < (N.filter (φ.colour · = c)).card := by
      obtain ⟨x, hx, hxc⟩ := hblocked c hc
      exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxc⟩⟩
    split <;> omega
  have hsum := Finset.sum_le_sum heach
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hsum
  have hones : (∑ c ∈ A, if (N.filter (φ.colour · = c)).card = 1 then 1 else 0) =
      (A.filter (fun c => (N.filter (φ.colour · = c)).card = 1)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hones] at hsum
  omega

def colouredNeighbours (φ : PartialColouring H F) (e : W) : Finset W := F.filter (H.Adj e)

def singleColours (φ : PartialColouring H F) (e : W) : Finset Colour :=
  Finset.univ.filter (fun c => ((φ.colouredNeighbours e).filter (φ.colour · = c)).card = 1)

theorem mem_singleColours (φ : PartialColouring H F) (e : W) (c : Colour) :
    c ∈ φ.singleColours e ↔ ∃ f, φ.Single e c f := by
  simp only [singleColours, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_one]
  constructor
  · rintro ⟨f, hf⟩
    have hfmem : f ∈ (φ.colouredNeighbours e).filter (φ.colour · = c) := by rw [hf]; simp
    simp only [colouredNeighbours, Finset.mem_filter] at hfmem
    refine ⟨f, ⟨hfmem.1.1, hfmem.1.2, hfmem.2⟩, ?_⟩
    intro g hg
    have : g ∈ (φ.colouredNeighbours e).filter (φ.colour · = c) := by
      simpa [colouredNeighbours] using And.intro (And.intro hg.1 hg.2.1) hg.2.2
    simpa [hf] using this
  · rintro ⟨f, hf, huniq⟩
    refine ⟨f, ?_⟩
    ext g
    simp only [Finset.mem_filter, colouredNeighbours, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hg, heg⟩, hc⟩
      exact huniq g ⟨hg, heg, hc⟩
    · rintro rfl
      exact ⟨⟨hf.1, hf.2.1⟩, hf.2.2⟩

theorem blocked_single_count (φ : PartialColouring H F) (e : W)
    (hb : ∀ c, ∃ g, φ.Neighbour e c g) :
    40 ≤ (φ.colouredNeighbours e).card + (φ.singleColours e).card := by
  have hh := φ.single_count (φ.colouredNeighbours e) Finset.univ (by
    intro c _
    obtain ⟨g, hg, heg, hc⟩ := hb c
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, heg⟩, hc⟩)
  simpa [singleColours] using hh

end PartialColouring

theorem at_least_sixteen_add_uncoloured_single {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) (e : G.edgeSet)
    (hb : ∀ c, ∃ g, φ.Neighbour e c g) :
    16 + ((conflicts G e) \ F).card ≤ (φ.singleColours e).card := by
  have hcount := φ.blocked_single_count e hb
  have hmax := card_conflicts_le_twentyFour G hΔ e
  have heq : φ.colouredNeighbours e = conflicts G e ∩ F := by
    ext g
    simp [PartialColouring.colouredNeighbours, and_comm]
  rw [heq] at hcount
  have hparts := Finset.card_sdiff_add_card_inter (conflicts G e) F
  omega

end Se20Insertion
