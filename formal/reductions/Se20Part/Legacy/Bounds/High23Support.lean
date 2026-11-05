module

public import Se20Part.Legacy.Bounds.High23Local

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rootLabels (Q : Finset G.edgeSet) (r : V) : Finset V :=
  (G.neighborFinset r).filter (fun a => ∃ e ∈ Q, e.val = s(r, a))

def rootType (r x : V) : Finset V :=
  (G.neighborFinset r).filter (G.Adj x)

omit [DecidableEq V] in
@[simp] theorem mem_rootType (r x a : V) :
    a ∈ rootType G r x ↔ G.Adj r a ∧ G.Adj x a := by
  simp [rootType]

theorem rootLabels_subset_neighbors (Q : Finset G.edgeSet) (r : V) :
    rootLabels G Q r ⊆ G.neighborFinset r := filter_subset _ _

theorem rootLabels_card (Q : Finset G.edgeSet) (r : V) :
    (rootLabels G Q r).card = (edgeIncidences G Q r).card := by
  classical
  symm
  let other := fun (e : G.edgeSet) (he : e ∈ edgeIncidences G Q r) =>
    Sym2.Mem.other ((mem_filter.mp he).2)
  have hs (e : G.edgeSet) (he : e ∈ edgeIncidences G Q r) :
      s(r, other e he) = e.val := Sym2.other_spec _
  apply card_bij other
  · intro e he
    exact mem_filter.mpr ⟨(G.mem_neighborFinset r _).mpr (G.mem_edgeSet.mp (hs e he ▸ e.property)),
      e, (mem_filter.mp he).1, (hs e he).symm⟩
  · intro e he f hf hef
    exact Subtype.ext ((hs e he).symm.trans (by rw [hef]; exact hs f hf))
  · intro a ha
    obtain ⟨_, e, heQ, hea⟩ := mem_filter.mp ha
    have he : e ∈ edgeIncidences G Q r :=
      mem_filter.mpr ⟨heQ, hea.symm ▸ Sym2.mem_mk_left r a⟩
    exact ⟨e, he, Sym2.congr_right.mp ((hs e he).trans hea)⟩

variable [DecidableRel (conflictGraph G).Adj]

theorem high23_root_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).Nonempty) : G.degree r = 4 := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨_, e, heQ, hea⟩ := mem_filter.mp ha
  exact (high23_endpoints_degree_four G hΔ e hea (h23 e heQ)).1

theorem high23_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) :
    G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb hab hAdj
  change G.Adj r a at ha
  change G.Adj r b at hb
  have hnot (x : V) (hx : x ∈ rootLabels G Q r) : x ≠ a ∧ x ≠ b := by
    obtain ⟨_, e, heQ, hex⟩ := mem_filter.mp hx
    constructor
    · intro hxa
      exact high23_no_triangle_on_edge G hΔ e (by simpa only [hxa] using hex)
        (h23 e heQ) hb hAdj
    · intro hxb
      exact high23_no_triangle_on_edge G hΔ e (by simpa only [hxb] using hex)
        (h23 e heQ) ha hAdj.symm
  have hs : rootLabels G Q r ⊆ ((G.neighborFinset r).erase a).erase b := by
    intro x hx
    exact mem_erase.mpr ⟨(hnot x hx).2, mem_erase.mpr ⟨(hnot x hx).1,
      rootLabels_subset_neighbors G Q r hx⟩⟩
  have hc := card_le_card hs
  have hca := card_erase_add_one ((G.mem_neighborFinset r a).mpr ha)
  have hcb := card_erase_add_one (mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset r b).mpr hb⟩)
  have hd := hΔ r
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
  omega

/-- The unique four-cycle budget of root label `a` identifies both the
other label and the exterior vertex of any two such two-step paths. -/
theorem high23_root_cross_unique
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    {r a b c x y : V} (ha : a ∈ rootLabels G Q r)
    (hb : G.Adj r b) (hc : G.Adj r c) (hba : b ≠ a) (hca : c ≠ a)
    (hxr : x ≠ r) (hyr : y ≠ r)
    (hax : G.Adj a x) (hbx : G.Adj b x)
    (hay : G.Adj a y) (hcy : G.Adj c y) : b = c ∧ x = y := by
  obtain ⟨_, e, heQ, hea⟩ := mem_filter.mp ha
  exact high23_cross_edges_unique G hΔ e hea (h23 e heQ)
    (mem_erase.mpr ⟨hba, (G.mem_neighborFinset r b).mpr hb⟩)
    (mem_erase.mpr ⟨hxr, (G.mem_neighborFinset a x).mpr hax⟩)
    (mem_erase.mpr ⟨hca, (G.mem_neighborFinset r c).mpr hc⟩)
    (mem_erase.mpr ⟨hyr, (G.mem_neighborFinset a y).mpr hay⟩) hbx hcy

omit [DecidableRel (conflictGraph G).Adj] in
theorem high23_type_meets_root_labels
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (r x : V) (hR : 3 ≤ (rootLabels G Q r).card)
    (hT : 2 ≤ (rootType G r x).card) :
    (rootType G r x ∩ rootLabels G Q r).Nonempty := by
  by_contra hn
  have hi : rootType G r x ∩ rootLabels G Q r = ∅ := not_nonempty_iff_eq_empty.mp hn
  have hs : rootType G r x ∪ rootLabels G Q r ⊆ G.neighborFinset r :=
    union_subset (filter_subset _ _) (rootLabels_subset_neighbors G Q r)
  have hc := card_le_card hs
  have hu := card_union_add_card_inter (rootType G r x) (rootLabels G Q r)
  have hd := hΔ r
  simp only [hi, card_empty, add_zero, SimpleGraph.card_neighborFinset_eq_degree] at hu hc
  omega

theorem high23_root_type_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card)
    {x : V} (hxr : x ≠ r) : (rootType G r x).card ≤ 2 := by
  by_contra hn
  obtain ⟨a, ha⟩ := high23_type_meets_root_labels G hΔ Q r x hR (by omega)
  obtain ⟨haT, haR⟩ := mem_inter.mp ha
  have herase := card_erase_add_one haT
  obtain ⟨b, hb, c, hc, hbc⟩ := one_lt_card.mp (show 1 < ((rootType G r x).erase a).card by omega)
  obtain ⟨hba, hbT⟩ := mem_erase.mp hb
  obtain ⟨hca, hcT⟩ := mem_erase.mp hc
  have hax := (mem_rootType G r x a).mp haT
  have hbx := (mem_rootType G r x b).mp hbT
  have hcx := (mem_rootType G r x c).mp hcT
  exact hbc (high23_root_cross_unique G hΔ Q h23 haR hbx.1 hcx.1 hba hca hxr hxr
    hax.2.symm hbx.2.symm hax.2.symm hcx.2.symm).1

theorem high23_double_type_unique
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    {r a x y : V} (ha : a ∈ rootLabels G Q r)
    (hxr : x ≠ r) (hyr : y ≠ r)
    (hax : a ∈ rootType G r x) (hay : a ∈ rootType G r y)
    (hx : 2 ≤ (rootType G r x).card) (hy : 2 ≤ (rootType G r y).card) : x = y := by
  obtain ⟨b, hb, hba⟩ := exists_mem_ne (show 1 < (rootType G r x).card by omega) a
  obtain ⟨c, hc, hca⟩ := exists_mem_ne (show 1 < (rootType G r y).card by omega) a
  obtain ⟨hrb, hxb⟩ := (mem_rootType G r x b).mp hb
  obtain ⟨hrc, hyc⟩ := (mem_rootType G r y c).mp hc
  exact (high23_root_cross_unique G hΔ Q h23 ha hrb hrc hba hca hxr hyr
    ((mem_rootType G r x a).mp hax).2.symm hxb.symm
    ((mem_rootType G r y a).mp hay).2.symm hyc.symm).2

theorem high23_type_singleton_of_sharing_double
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    {r a p x : V} (ha : a ∈ rootLabels G Q r)
    (hpr : p ≠ r) (hxr : x ≠ r) (hpx : p ≠ x)
    (hpa : a ∈ rootType G r p) (hxa : a ∈ rootType G r x)
    (hp : 2 ≤ (rootType G r p).card) : rootType G r x = {a} := by
  have hc : (rootType G r x).card ≤ 1 := by
    by_contra hn
    exact hpx (high23_double_type_unique G hΔ Q h23 ha hpr hxr hpa hxa hp (by omega))
  apply eq_singleton_iff_unique_mem.mpr
  exact ⟨hxa, fun b hb => card_le_one.mp hc b hb a hxa⟩

end Se20Part.Legacy
