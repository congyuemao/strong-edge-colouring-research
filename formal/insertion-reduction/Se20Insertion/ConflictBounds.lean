import Se20Insertion.GraphBasics

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def incident (v : V) : Finset G.edgeSet := Finset.univ.filter (fun e => v ∈ e.val)

@[simp] theorem mem_incident (v : V) (e : G.edgeSet) :
    e ∈ incident G v ↔ v ∈ e.val := by simp [incident]

theorem card_incident (v : V) : (incident G v).card = G.degree v := by
  have him : (incident G v).image Subtype.val = G.incidenceFinset v := by
    ext e
    simp only [Finset.mem_image, mem_incident, SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f.2, hf⟩
    · rintro ⟨he, hv⟩
      exact ⟨⟨e, he⟩, hv, rfl⟩
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, ← him,
    Finset.card_image_of_injective _ Subtype.val_injective]

def rim (u v : V) : Finset V :=
  (G.neighborFinset u).erase v ∪ (G.neighborFinset v).erase u

def conflicts (e : G.edgeSet) : Finset G.edgeSet := Finset.univ.filter ((L2 G).Adj e)

@[simp] theorem mem_conflicts (e f : G.edgeSet) : f ∈ conflicts G e ↔ (L2 G).Adj e f := by
  simp [conflicts]

/-- The endpoint-neighbour cover has no edge-deletion interpretation. -/
theorem conflicts_eq_rim (e : G.edgeSet) {u v : V} (he : e.val = s(u, v)) :
    conflicts G e = (rim G u v).biUnion (incident G) := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  have atEndpoint : ∀ {a b : V} (f : G.edgeSet), e.val = s(a, b) → a ∈ f.val → e ≠ f →
      ∃ x ∈ (G.neighborFinset a).erase b, x ∈ f.val := by
    intro a b f he' haf hne
    obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp haf
    have hax : G.Adj a x := G.mem_edgeSet.mp (hx ▸ f.2)
    have hxb : x ≠ b := by
      intro h; subst x
      exact hne (Subtype.ext (he'.trans hx.symm))
    exact ⟨x, by simp [hxb, hax], hx ▸ Sym2.mem_mk_right a x⟩
  have rim_ne : ∀ x ∈ rim G u v, x ≠ u ∧ x ≠ v := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx := Finset.mem_erase.mp hx
      exact ⟨((G.mem_neighborFinset _ _).mp hx.2).ne.symm, hx.1⟩
    · have hx := Finset.mem_erase.mp hx
      exact ⟨hx.1, ((G.mem_neighborFinset _ _).mp hx.2).ne.symm⟩
  ext f
  simp only [mem_conflicts, Finset.mem_biUnion, mem_incident]
  constructor
  · rintro ⟨hne, a, ha, b, hb, hab⟩
    rw [he, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · rcases hab with h | h
      · subst b
        obtain ⟨x, hx, hxf⟩ := atEndpoint f he hb hne
        exact ⟨x, Finset.mem_union_left _ hx, hxf⟩
      · by_cases hbv : b = v
        · subst b
          obtain ⟨x, hx, hxf⟩ := atEndpoint f (he.trans Sym2.eq_swap) hb hne
          exact ⟨x, Finset.mem_union_right _ hx, hxf⟩
        · exact ⟨b, Finset.mem_union_left _ (by simp [hbv, h]), hb⟩
    · rcases hab with h | h
      · subst b
        obtain ⟨x, hx, hxf⟩ := atEndpoint f (he.trans Sym2.eq_swap) hb hne
        exact ⟨x, Finset.mem_union_right _ hx, hxf⟩
      · by_cases hbu : b = u
        · subst b
          obtain ⟨x, hx, hxf⟩ := atEndpoint f he hb hne
          exact ⟨x, Finset.mem_union_left _ hx, hxf⟩
        · exact ⟨b, Finset.mem_union_right _ (by simp [hbu, h]), hb⟩
  · rintro ⟨x, hx, hxf⟩
    have hne : e ≠ f := by
      intro h; subst f
      rw [he, Sym2.mem_iff] at hxf
      exact hxf.elim (rim_ne x hx).1 (rim_ne x hx).2
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨hne, u, he ▸ Sym2.mem_mk_left u v, x, hxf,
        Or.inr ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hx).2)⟩
    · exact ⟨hne, v, he ▸ Sym2.mem_mk_right u v, x, hxf,
        Or.inr ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hx).2)⟩

theorem card_rim_le_six (hΔ : MaxDegreeFour G) {u v : V} (huv : G.Adj u v) :
    (rim G u v).card ≤ 6 := by
  have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  have hc := Finset.card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdu hdv
  dsimp [rim]
  omega

theorem card_rim_le_five (hΔ : MaxDegreeFour G) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (rim G u v).card ≤ 5 := by
  have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  have hc := Finset.card_union_add_card_inter ((G.neighborFinset u).erase v)
    ((G.neighborFinset v).erase u)
  have hpos : 0 < (((G.neighborFinset u).erase v) ∩ ((G.neighborFinset v).erase u)).card := by
    apply Finset.card_pos.mpr
    exact ⟨w, by simp [huw, hvw, huw.ne.symm, hvw.ne.symm]⟩
  have hdu := hΔ u
  have hdv := hΔ v
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdu hdv
  dsimp [rim]
  omega

theorem card_conflicts_le_mul_rim (hΔ : MaxDegreeFour G) (e : G.edgeSet)
    {u v : V} (he : e.val = s(u, v)) :
    (conflicts G e).card ≤ (rim G u v).card * 4 := by
  rw [conflicts_eq_rim G e he]
  calc
    _ ≤ ∑ x ∈ rim G u v, (incident G x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ rim G u v, 4 := Finset.sum_le_sum (fun x _ => by simpa [card_incident] using hΔ x)
    _ = _ := by simp

theorem card_conflicts_le_twentyFour (hΔ : MaxDegreeFour G) (e : G.edgeSet) :
    (conflicts G e).card ≤ 24 := by
  obtain ⟨u, v, he⟩ : ∃ u v, e.val = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  exact (card_conflicts_le_mul_rim G hΔ e he).trans (by
    have := card_rim_le_six G hΔ huv
    omega)

theorem card_conflicts_triangle_le_twenty (hΔ : MaxDegreeFour G)
    (e : G.edgeSet) (ht : OnTriangle G e) : (conflicts G e).card ≤ 20 := by
  obtain ⟨u, v, w, he, huw, hvw⟩ := ht
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  exact (card_conflicts_le_mul_rim G hΔ e he).trans (by
    have := card_rim_le_five G hΔ huv huw hvw
    omega)

end Se20Insertion
