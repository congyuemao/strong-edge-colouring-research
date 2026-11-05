module

public import Se20Part.Legacy.Bounds.ConflictDegree

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

theorem card_le_via_relation {α β : Type*} (s : Finset α) (t : Finset β)
    (R : α → β → Prop) (hex : ∀ a ∈ s, ∃ b ∈ t, R a b)
    (hinj : ∀ a ∈ s, ∀ a' ∈ s, ∀ b, R a b → R a' b → a = a') : s.card ≤ t.card := by
  classical
  choose f hmem hrel using hex
  let g : s → t := fun a => ⟨f a.val a.property, hmem a.val a.property⟩
  apply card_le_card_of_injective (f := g)
  intro a a' heq
  apply Subtype.ext
  have hf : f a.val a.property = f a'.val a'.property := congrArg Subtype.val heq
  exact hinj a.val a.property a'.val a'.property _ (hrel a.val a.property)
    (hf.symm ▸ hrel a'.val a'.property)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def edgeIncidences (Q : Finset G.edgeSet) (v : V) : Finset G.edgeSet :=
  Q.filter (fun e => v ∈ e.val)

def edgesMeeting (Q : Finset G.edgeSet) (S : Finset V) : Finset G.edgeSet :=
  Q.filter (fun e => ∃ v ∈ S, v ∈ e.val)

def edgesInside (Q : Finset G.edgeSet) (S : Finset V) : Finset G.edgeSet :=
  Q.filter (fun e => ∀ v ∈ e.val, v ∈ S)

theorem edgeIncidences_univ_card (v : V) :
    (edgeIncidences G univ v).card = G.degree v := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  apply card_bij (fun e _ => e.val)
  · intro e he
    exact G.mem_incidenceFinset.mpr ⟨e.property, (mem_filter.mp he).2⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro f hf
    obtain ⟨hfg, hvf⟩ := G.mem_incidenceFinset.mp hf
    exact ⟨⟨f, hfg⟩, mem_filter.mpr ⟨mem_univ _, hvf⟩, rfl⟩

theorem edgeIncidences_card_le_degree (Q : Finset G.edgeSet) (v : V) :
    (edgeIncidences G Q v).card ≤ G.degree v := by
  rw [← edgeIncidences_univ_card G v]
  apply card_le_card
  intro e he
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩

omit [DecidableRel G.Adj] in
theorem edge_endpoint_count (S : Finset V) (e : G.edgeSet) :
    (S.filter (fun v => v ∈ e.val)).card =
      (if ∃ v ∈ S, v ∈ e.val then 1 else 0) +
      (if ∀ v ∈ e.val, v ∈ S then 1 else 0) := by
  classical
  obtain ⟨a, b, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hab : G.Adj a b := G.mem_edgeSet.mp (he ▸ e.property)
  have hfilter : S.filter (fun v => v ∈ e.val) = ({a, b} : Finset V).filter (fun v => v ∈ S) := by
    ext v
    simp only [← he, Sym2.mem_iff, mem_filter, mem_insert, mem_singleton]
    tauto
  have hex : (∃ v ∈ S, v ∈ e.val) ↔ a ∈ S ∨ b ∈ S := by
    simp only [← he, Sym2.mem_iff, and_or_left, exists_or, exists_eq_right]
  rw [hfilter, if_congr hex rfl rfl]
  simp only [← he, Sym2.forall_mem_pair]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    simp [filter_insert, filter_singleton, ha, hb, hab.ne]

omit [DecidableRel G.Adj] in
/-- An edge meeting the set is counted once, with one extra count exactly
when both endpoints lie in the set. All edges are original graph edges. -/
theorem incidence_sum_eq_meeting_add_inside (Q : Finset G.edgeSet) (S : Finset V) :
    (∑ v ∈ S, (edgeIncidences G Q v).card) =
      (edgesMeeting G Q S).card + (edgesInside G Q S).card := by
  classical
  have hswap : (∑ v ∈ S, (edgeIncidences G Q v).card) =
      ∑ e ∈ Q, (S.filter (fun v => v ∈ e.val)).card := by
    simp only [edgeIncidences, card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [hswap]
  simp only [edgesMeeting, edgesInside, card_eq_sum_ones, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  simpa only [card_eq_sum_ones, sum_filter] using edge_endpoint_count G S e

theorem conflict_degree_add_inside_le_sum
    [DecidableRel (conflictGraph G).Adj] {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) :
    (conflictGraph G).degree e + (edgesInside G univ (endpointNeighbourCover G u v)).card ≤
      ∑ w ∈ endpointNeighbourCover G u v, G.degree w := by
  classical
  have hs : (conflictGraph G).neighborFinset e ⊆
      edgesMeeting G univ (endpointNeighbourCover G u v) := by
    intro f hf
    exact mem_filter.mpr ⟨mem_univ _, strongConflict_meets_cover G he
      (((conflictGraph G).mem_neighborFinset e f).mp hf)⟩
  have hc := card_le_card hs
  have hsum := incidence_sum_eq_meeting_add_inside G univ (endpointNeighbourCover G u v)
  simp only [edgeIncidences_univ_card] at hsum
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

theorem clique_card_le_one_add_incidence_sum
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v)) :
    Q.card ≤ 1 + ∑ w ∈ endpointNeighbourCover G u v, (edgeIncidences G Q w).card := by
  classical
  have hs : Q.erase e ⊆ edgesMeeting G Q (endpointNeighbourCover G u v) := by
    intro f hf
    obtain ⟨hne, hfQ⟩ := mem_erase.mp hf
    exact mem_filter.mpr ⟨hfQ, strongConflict_meets_cover G he (hQ heQ hfQ hne.symm)⟩
  have hc := card_le_card hs
  have hsum := incidence_sum_eq_meeting_add_inside G Q (endpointNeighbourCover G u v)
  have hec := card_erase_add_one heQ
  omega

theorem clique_card_le_thirteen_of_support_degree_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 2) : Q.card ≤ 13 := by
  by_cases hQempty : Q = ∅
  · simp [hQempty]
  obtain ⟨e, heQ⟩ := nonempty_iff_ne_empty.mpr hQempty
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := clique_card_le_one_add_incidence_sum G Q hQ e heQ he.symm
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hQdeg w)
  have hcard := endpointNeighbourCover_card_le_six G huv hΔ
  simp only [sum_const, smul_eq_mul] at hs
  omega

end Se20Part.Legacy
