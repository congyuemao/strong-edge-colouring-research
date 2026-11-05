import Se20Insertion.SingleChains
import Mathlib.Combinatorics.Hall.Finite

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem card_rim_le_degrees {u v : V} (huv : G.Adj u v) :
    (rim G u v).card + 2 ≤ G.degree u + G.degree v := by
  have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  have hc := Finset.card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  dsimp [rim]; omega

/-- The first conclusion of 11.22, including saturation of all twenty members. -/
theorem degree_three_saturated (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) (e : G.edgeSet) {u v : V}
    (he : e.val = s(u,v)) (hu : G.degree u ≤ 3)
    (hb : ∀ c, ∃ f, φ.Neighbour e c f)
    (hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b) :
    (conflicts G e).card = 20 ∧ (∀ f ∈ conflicts G e, f ∈ F) ∧
      Set.InjOn φ.colour (conflicts G e) ∧
      ∀ f ∈ conflicts G e, ∀ c, c ≠ φ.colour f → ∃ x, φ.Neighbour f c x := by
  have hr := card_rim_le_degrees G (G.mem_edgeSet.mp (he ▸ e.2))
  have hm := card_conflicts_le_mul_rim G hΔ e he
  have hv := hΔ v
  obtain ⟨hn, hF, hinj⟩ := φ.saturated_twenty (conflicts G e) e (mem_conflicts G e)
    (by omega) hb
  refine ⟨hn, hF, hinj, ?_⟩
  intro f hf c hc
  apply φ.single_saturated_of_no_trivial (p := φ.colour f) (f := f) _ hnt c hc
  refine ⟨⟨hF f hf, (mem_conflicts G _ _).mp hf, rfl⟩, ?_⟩
  intro x hx
  exact hinj ((mem_conflicts G _ _).mpr hx.2.1) hf hx.2.2

/-- Coloured conflicts after deleting the whole star at u. -/
theorem star_coloured_conflicts_le (hΔ : MaxDegreeFour G)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F) (u : V)
    (hF : Disjoint F (incident G u)) (e : G.edgeSet) (he : u ∈ e.val) :
    (φ.colouredNeighbours e).card ≤ 3 * G.degree u + 9 := by
  obtain ⟨v, hv⟩ := Sym2.mem_iff_exists.mp he
  have huv : G.Adj u v := G.mem_edgeSet.mp (hv ▸ e.2)
  have hr := card_rim_le_degrees G huv
  have hm := card_conflicts_le_mul_rim G hΔ e hv
  have hd := hΔ v
  have hsub : (incident G u).erase e ⊆ conflicts G e \ F := by
    intro f hf
    obtain ⟨hfe, hfu⟩ := Finset.mem_erase.mp hf
    refine Finset.mem_sdiff.mpr ⟨(mem_conflicts G e f).mpr
      ⟨hfe.symm, u, he, u, (mem_incident G _ _).mp hfu, Or.inl rfl⟩, ?_⟩
    exact fun hfF => Finset.disjoint_left.mp hF hfF hfu
  have hle := Finset.card_le_card hsub
  have hi := Finset.card_erase_add_one ((mem_incident G u e).mpr he)
  rw [card_incident] at hi
  have hp := Finset.card_sdiff_add_card_inter (conflicts G e) F
  have hN : φ.colouredNeighbours e = conflicts G e ∩ F := by
    ext f; simp [PartialColouring.colouredNeighbours, and_comm]
  rw [← hN] at hp
  omega

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def available (φ : PartialColouring H F) (v : W) : Finset Colour :=
  Finset.univ.filter (φ.Free v)

theorem available_card (φ : PartialColouring H F) (v : W) :
    20 ≤ (φ.available v).card + (φ.colouredNeighbours v).card := by
  have heq : φ.available v = Finset.univ \ (φ.colouredNeighbours v).image φ.colour := by
    ext c; simp [available, Free, Neighbour, colouredNeighbours, and_assoc]
  have hparts := Finset.card_sdiff_add_card_inter (Finset.univ : Finset Colour)
    ((φ.colouredNeighbours v).image φ.colour)
  rw [← heq, Finset.univ_inter] at hparts
  have hi := Finset.card_image_le (s := φ.colouredNeighbours v) (f := φ.colour)
  have hc : (Finset.univ : Finset Colour).card = 20 := rfl
  omega

/-- An injective choice of free colours extends a partial colouring. -/
theorem extend_by_lists [DecidableEq W] (φ : PartialColouring H F) (U : Finset W)
    (c : U → Colour) (hinj : Function.Injective c)
    (hfree : ∀ x : U, φ.Free x.val (c x)) :
    Nonempty (PartialColouring H (F ∪ U)) := by
  refine ⟨⟨fun x => if hx : x ∈ U then c ⟨x,hx⟩ else φ.colour x, ?_⟩⟩
  intro x y hx hy hxy heq
  by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
  · have hc : c ⟨x,hxU⟩ = c ⟨y,hyU⟩ := by simpa [hxU,hyU] using heq
    exact hxy.ne (congrArg Subtype.val (hinj hc))
  · exact hfree ⟨x,hxU⟩ ⟨y, (Finset.mem_union.mp hy).resolve_right hyU, hxy,
      by simpa [hxU,hyU] using heq.symm⟩
  · exact hfree ⟨y,hyU⟩ ⟨x, (Finset.mem_union.mp hx).resolve_right hxU, hxy.symm,
      by simpa [hxU,hyU] using heq⟩
  · exact φ.proper ((Finset.mem_union.mp hx).resolve_right hxU)
      ((Finset.mem_union.mp hy).resolve_right hyU) hxy (by simpa [hxU,hyU] using heq)

end PartialColouring

/-- Hall's theorem for n lists of size at least n-1: the only obstruction
is a common list of size n-1. Used with n=3 (11.24) and n=6 (11.41). -/
theorem almost_full_lists {I A : Type*} [Fintype I] [Nonempty I]
    (L : I → Finset A) (hL : ∀ i, Fintype.card I - 1 ≤ (L i).card)
    (hno : ¬ ∃ c : I → A, Function.Injective c ∧ ∀ i, c i ∈ L i) :
    ∃ S : Finset A, S.card = Fintype.card I - 1 ∧ ∀ i, L i = S := by
  have hn : ¬ ∀ s : Finset I, s.card ≤ (s.biUnion L).card := by
    intro h
    exact hno ((Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp h)
  push_neg at hn
  obtain ⟨s, hs⟩ := hn
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  have hsub : L i ⊆ s.biUnion L := Finset.subset_biUnion_of_mem L hi
  have hle := (hL i).trans (Finset.card_le_card hsub)
  have hsmax := Finset.card_le_univ s
  have hsall : s = Finset.univ := Finset.eq_univ_of_card s (by omega)
  subst s
  refine ⟨Finset.univ.biUnion L, by omega, ?_⟩
  intro j
  exact Finset.eq_of_subset_of_card_le (Finset.subset_biUnion_of_mem L (Finset.mem_univ j))
    (by have := hL j; omega)

/-- Lemma 11.24(1), for the ambient partial colouring obtained from G-u.
The exact obstruction is all three lists equal to one two-element set. -/
theorem degree_three_lists (hΔ : MaxDegreeFour G) (u : V) (hu : G.degree u = 3)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (hF : Disjoint F (incident G u)) :
    (∀ e ∈ incident G u, 2 ≤ (φ.available e).card) ∧
    (¬ Nonempty (PartialColouring (L2 G) (F ∪ incident G u)) →
      ∃ S : Finset Colour, S.card = 2 ∧ ∀ e ∈ incident G u, φ.available e = S) := by
  have hL : ∀ e ∈ incident G u, 2 ≤ (φ.available e).card := by
    intro e he
    have hc := star_coloured_conflicts_le G hΔ φ u hF e ((mem_incident G _ _).mp he)
    have ha := φ.available_card e
    omega
  refine ⟨hL, ?_⟩
  intro hno
  have hn : Fintype.card (incident G u) = 3 := by
    rw [Fintype.card_coe, card_incident, hu]
  haveI : Nonempty (incident G u) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S,hS,heq⟩ := almost_full_lists (fun e : incident G u => φ.available e.val)
    (by intro e; rw [hn]; exact hL e.val e.property) (by
      rintro ⟨c, hc, hf⟩
      exact hno (φ.extend_by_lists (incident G u) c hc
        (fun e => (Finset.mem_filter.mp (hf e)).2)))
  exact ⟨S, by rw [hn] at hS; exact hS, fun e he => heq ⟨e,he⟩⟩

/-- The low-degree extension used by 11.25(1). -/
theorem strongColourable_of_delete_lowDegree (hΔ : MaxDegreeFour G) (u : V)
    (hu : G.degree u ≤ 2) (hc : StrongColourable (G.induce {x | x ≠ u}) 20) :
    StrongColourable G 20 := by
  obtain ⟨φ⟩ := starColouring_of_deleteColourable G u hc
  let U := incident G u
  have hlist : ∀ e : U, U.card ≤ (φ.available e.val).card := by
    intro e
    have hh := star_coloured_conflicts_le G hΔ φ u (Finset.disjoint_sdiff.symm)
      e.val ((mem_incident G _ _).mp e.property)
    have ha := φ.available_card e.val
    have hU : U.card = G.degree u := card_incident G u
    omega
  obtain ⟨c, hinj, hfree⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun e : U => φ.available e.val)).mp (by
      intro S
      by_cases hS : S.Nonempty
      · obtain ⟨e,he⟩ := hS
        have hsub := Finset.card_le_card (Finset.subset_biUnion_of_mem
          (fun e : U => φ.available e.val) he)
        have hcard := Finset.card_le_univ S
        rw [Fintype.card_coe] at hcard
        exact hcard.trans ((hlist e).trans hsub)
      · simp_all)
  obtain ⟨ψ⟩ := φ.extend_by_lists U c hinj (fun e => (Finset.mem_filter.mp (hfree e)).2)
  have hdom : (Finset.univ \ incident G u) ∪ U = Finset.univ := by simp [U]
  exact ⟨SimpleGraph.Coloring.mk ψ.colour (fun {e f} hef =>
    ψ.proper (by rw [hdom]; simp) (by rw [hdom]; simp) hef)⟩

theorem minimal_counterexample_minDegree (hΔ : MaxDegreeFour G)
    (hno : ¬ StrongColourable G 20)
    (hdel : ∀ u, StrongColourable (G.induce {x | x ≠ u}) 20) :
    ∀ u, 3 ≤ G.degree u := by
  intro u
  by_contra h
  exact hno (strongColourable_of_delete_lowDegree G hΔ u (by omega) (hdel u))

end Se20Insertion
