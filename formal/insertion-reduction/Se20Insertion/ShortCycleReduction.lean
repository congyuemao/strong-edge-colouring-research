import Se20Insertion.StarGeometry
import Se20Insertion.ListExtensions

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem star_coloured_conflicts_subtract {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) (u : V) (hF : Disjoint F (incident G u))
    (e : G.edgeSet) (he : u ∈ e.val) :
    (φ.colouredNeighbours e).card + G.degree u ≤ (conflicts G e).card + 1 := by
  have hsub : (incident G u).erase e ⊆ conflicts G e \ F := by
    intro f hf
    obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hf
    exact Finset.mem_sdiff.mpr ⟨(mem_conflicts G e f).mpr
      ⟨hne.symm,u,he,u,(mem_incident G u f).mp hu,Or.inl rfl⟩,
      fun h => Finset.disjoint_left.mp hF h hu⟩
  have hs := Finset.card_le_card hsub
  have hi := Finset.card_erase_add_one ((mem_incident G u e).mpr he)
  rw [card_incident] at hi
  have hp := Finset.card_sdiff_add_card_inter (conflicts G e) F
  have hn : φ.colouredNeighbours e = conflicts G e ∩ F := by
    ext f; simp [PartialColouring.colouredNeighbours,and_comm]
  rw [← hn] at hp; omega

theorem degree_three_triangle_conflicts (hΔ : MaxDegreeFour G) {u v w : V}
    (hu : G.degree u = 3) (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (conflicts G (edge G huv)).card ≤ 16 := by
  have hi := Finset.card_union_add_card_inter ((G.neighborFinset u).erase v)
    ((G.neighborFinset v).erase u)
  have hp : 1 ≤ (((G.neighborFinset u).erase v) ∩ ((G.neighborFinset v).erase u)).card :=
    Finset.card_pos.mpr ⟨w, by simp [huw,hvw,huw.ne.symm,hvw.ne.symm]⟩
  have hc := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hd := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  rw [SimpleGraph.card_neighborFinset_eq_degree,hu] at hc
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hd
  have hv := hΔ v
  have hr : (rim G u v).card ≤ 4 := by dsimp [rim]; omega
  have hn := card_conflicts_le_mul_rim G hΔ (edge G huv) rfl
  omega

/-- A four-cycle through u gives a counted-twice edge inside the rim.
Additional chords and identifications elsewhere only improve the bound. -/
theorem degree_three_square_conflicts (hΔ : MaxDegreeFour G) {u v w x : V}
    (hu : G.degree u = 3) (huv : G.Adj u v) (hvw : G.Adj v w)
    (hwx : G.Adj w x) (hxu : G.Adj x u) (huw : u ≠ w) (hvx : v ≠ x) :
    (conflicts G (edge G huv)).card ≤ 19 := by
  have hr := card_rim_le_degrees G huv
  have hv := hΔ v
  have hs : (∑ a ∈ rim G u v, incidenceCount G Finset.univ a) ≤ (rim G u v).card * 4 := by
    calc
      _ ≤ ∑ _a ∈ rim G u v, 4 := Finset.sum_le_sum (fun a _ => by
        simpa [incidenceCount,card_incident] using hΔ a)
      _ = _ := by simp
  have hp : 1 ≤ (internalEdges G Finset.univ (rim G u v)).card := by
    apply Finset.card_pos.mpr
    refine ⟨edge G hwx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro a ha
    simp only [edge,Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_union_right _ (by simp [huw.symm,hvw])
    · exact Finset.mem_union_left _ (by simp [hvx.symm,hxu.symm])
  have hi := rim_incidence_identity G Finset.univ (edge G huv) rfl
  change _ = (conflicts G (edge G huv)).card + _ at hi
  omega

theorem degree_three_extension_of_small_conflicts (hΔ : MaxDegreeFour G) {u : V}
    (hu : G.degree u = 3) {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (hF : Disjoint F (incident G u)) {e : G.edgeSet} (he : u ∈ e.val)
    (hn : (conflicts G e).card ≤ 19) :
    ∃ ψ : PartialColouring (L2 G) (F ∪ incident G u), ∀ x ∈ F, ψ.colour x = φ.colour x := by
  have hc := star_coloured_conflicts_subtract G φ u hF e he
  have hl := φ.available_card e
  apply degree_three_direct_extension G hΔ u hu φ hF
  rintro ⟨S,hS,hall⟩
  have heq := hall e ((mem_incident G u e).mpr he)
  rw [heq,hS] at hl
  omega

theorem degree_three_short_cycle_reducible (hΔ : MaxDegreeFour G) {u : V}
    (hu : G.degree u = 3) (hc : StrongColourable (G.induce {x | x ≠ u}) 20)
    (hshort : (∃ v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w) ∨
      ∃ v w x, G.Adj u v ∧ G.Adj v w ∧ G.Adj w x ∧ G.Adj x u ∧ u ≠ w ∧ v ≠ x) :
    StrongColourable G 20 := by
  obtain ⟨φ⟩ := starColouring_of_deleteColourable G u hc
  have hex : ∃ e : G.edgeSet, u ∈ e.val ∧ (conflicts G e).card ≤ 19 := by
    rcases hshort with ⟨v,w,huv,huw,hvw⟩ | ⟨v,w,x,huv,hvw,hwx,hxu,huw,hvx⟩
    · exact ⟨edge G huv, by simp [edge], (degree_three_triangle_conflicts G hΔ hu huv huw hvw).trans (by decide)⟩
    · exact ⟨edge G huv, by simp [edge], degree_three_square_conflicts G hΔ hu huv hvw hwx hxu huw hvx⟩
  obtain ⟨e,he,hn⟩ := hex
  obtain ⟨ψ,_⟩ := degree_three_extension_of_small_conflicts G hΔ hu φ
    Finset.disjoint_sdiff.symm he hn
  have hdom : (Finset.univ \ incident G u) ∪ incident G u = Finset.univ := by simp
  exact ⟨SimpleGraph.Coloring.mk ψ.colour (fun {e f} hef =>
    ψ.proper (by rw [hdom]; simp) (by rw [hdom]; simp) hef)⟩

/-- 11.25(2), using only vertex deletion minimality. -/
theorem minimal_counterexample_degree_three_no_short_cycle (hΔ : MaxDegreeFour G)
    (hno : ¬ StrongColourable G 20)
    (hdel : ∀ u, StrongColourable (G.induce {x | x ≠ u}) 20) {u : V} (hu : G.degree u = 3) :
    (∀ v w, G.Adj u v → G.Adj u w → ¬ G.Adj v w) ∧
    ∀ v w x, G.Adj u v → G.Adj v w → G.Adj w x → G.Adj x u → u ≠ w → v ≠ x → False := by
  constructor
  · intro v w huv huw hvw
    exact hno (degree_three_short_cycle_reducible G hΔ hu (hdel u) (Or.inl ⟨v,w,huv,huw,hvw⟩))
  · intro v w x huv hvw hwx hxu huw hvx
    exact hno (degree_three_short_cycle_reducible G hΔ hu (hdel u) (Or.inr ⟨v,w,x,huv,hvw,hwx,hxu,huw,hvx⟩))

end Se20Insertion
