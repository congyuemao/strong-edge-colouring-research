module

public import Se20Part.Legacy.Bounds.ConflictRigidity

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem conflict_degree_eq_24_of_ge
    (hΔ : ∀ x, G.degree x ≤ 4) (e : G.edgeSet)
    (h : 24 ≤ (conflictGraph G).degree e) :
    (conflictGraph G).degree e = 24 :=
  Nat.le_antisymm (conflict_degree_le_24 G hΔ e) h

/-- Edges in a branch at `a`, excluding the edge back to its centre `u`.
Membership in `Q` never changes the original graph used for conflicts. -/
def branchEdges (Q : Finset G.edgeSet) (u a : V) : Finset G.edgeSet :=
  Q.filter (fun e => a ∈ e.val ∧ u ∉ e.val)

omit [Fintype V] [DecidableRel G.Adj] [DecidableRel (conflictGraph G).Adj] in
@[simp] theorem mem_branchEdges (Q : Finset G.edgeSet) (u a : V) (e : G.edgeSet) :
    e ∈ branchEdges G Q u a ↔ e ∈ Q ∧ a ∈ e.val ∧ u ∉ e.val := by
  simp [branchEdges]

/-- A degree-24 edge cannot join two neighbours of a common vertex. -/
theorem high24_edge_not_between_neighbors
    (hΔ : ∀ x, G.degree x ≤ 4) {u a b : V} (e : G.edgeSet)
    (he : e.val = s(a, b)) (h24 : (conflictGraph G).degree e = 24)
    (hua : G.Adj u a) (hub : G.Adj u b) : False := by
  have hab : G.Adj a b := G.mem_edgeSet.mp (he ▸ e.property)
  exact endpoint_neighborhood_independent_of_degree_eq_24 G hΔ e he h24
    hua.symm hab hub.ne hub

/-- Conflicting degree-24 edges from distinct branches must have adjacent
outer endpoints. All other conflict witnesses are excluded by local rigidity. -/
theorem high24_external_conflict_adj
    (hΔ : ∀ x, G.degree x ≤ 4) {u a b x y : V} (e f : G.edgeSet)
    (he : e.val = s(a, x)) (hf : f.val = s(b, y))
    (he24 : (conflictGraph G).degree e = 24)
    (hf24 : (conflictGraph G).degree f = 24)
    (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b)
    (hxu : x ≠ u) (hyu : y ≠ u) (hc : StrongConflict G e f) : G.Adj x y := by
  have hnab : ¬ G.Adj a b := by
    intro h
    exact endpoint_neighborhood_independent_of_degree_eq_24 G hΔ e he he24
      hua.symm h hub.ne hub
  have hnxb : ¬ G.Adj x b := by
    intro h
    exact no_cross_edge_of_degree_eq_24 G hΔ e he he24
      (mem_erase.mpr ⟨hxu.symm, (G.mem_neighborFinset a u).mpr hua.symm⟩)
      (mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset x b).mpr h⟩) hub
  have hnay : ¬ G.Adj a y := by
    intro h
    exact no_cross_edge_of_degree_eq_24 G hΔ f hf hf24
      (mem_erase.mpr ⟨hyu.symm, (G.mem_neighborFinset b u).mpr hub.symm⟩)
      (mem_erase.mpr ⟨hab, (G.mem_neighborFinset y a).mpr h.symm⟩) hua
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he hc
  rw [hf, Sym2.mem_iff] at hwf
  rcases hwf with hwb | hwy
  · have hb : b ∈ endpointNeighbourCover G a x := hwb ▸ hw
    rcases mem_union.mp hb with h | h
    · exact (hnab ((G.mem_neighborFinset a b).mp (mem_erase.mp h).2)).elim
    · exact (hnxb ((G.mem_neighborFinset x b).mp (mem_erase.mp h).2)).elim
  · have hy : y ∈ endpointNeighbourCover G a x := hwy ▸ hw
    rcases mem_union.mp hy with h | h
    · exact (hnay ((G.mem_neighborFinset a y).mp (mem_erase.mp h).2)).elim
    · exact (G.mem_neighborFinset x y).mp (mem_erase.mp h).2

theorem high24_distinct_branches_ne
    (hΔ : ∀ x, G.degree x ≤ 4) {u a b : V} (e f : G.edgeSet)
    (he24 : (conflictGraph G).degree e = 24)
    (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b)
    (ha : a ∈ e.val) (hb : b ∈ f.val) : e ≠ f := by
  intro hef
  have hb' : b ∈ e.val := hef ▸ hb
  exact high24_edge_not_between_neighbors G hΔ e
    ((Sym2.mem_and_mem_iff hab).mp ⟨ha, hb'⟩) he24 hua hub

/-- Two edges in one branch exclude any edge in a different branch of the
same centre, provided the edges form a clique and all have full degree 24. -/
theorem high24_mixed_branches_cannot_have_fork
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, (conflictGraph G).degree e = 24)
    {u a b : V} (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b)
    (e₁ e₂ f : G.edgeSet) (h₁ : e₁ ∈ branchEdges G Q u a)
    (h₂ : e₂ ∈ branchEdges G Q u a) (hf : f ∈ branchEdges G Q u b)
    (hne : e₁ ≠ e₂) : False := by
  obtain ⟨h₁Q, h₁a, h₁u⟩ := (mem_branchEdges G Q u a e₁).mp h₁
  obtain ⟨h₂Q, h₂a, h₂u⟩ := (mem_branchEdges G Q u a e₂).mp h₂
  obtain ⟨hfQ, hfb, hfu⟩ := (mem_branchEdges G Q u b f).mp hf
  obtain ⟨x₁, hx₁⟩ := Sym2.mem_iff_exists.mp h₁a
  obtain ⟨x₂, hx₂⟩ := Sym2.mem_iff_exists.mp h₂a
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hfb
  have hx₁u : x₁ ≠ u := by
    intro h
    apply h₁u
    rw [hx₁, h]
    exact Sym2.mem_mk_right _ _
  have hx₂u : x₂ ≠ u := by
    intro h
    apply h₂u
    rw [hx₂, h]
    exact Sym2.mem_mk_right _ _
  have hyu : y ≠ u := by
    intro h
    apply hfu
    rw [hy, h]
    exact Sym2.mem_mk_right _ _
  have h₁f := high24_distinct_branches_ne G hΔ e₁ f (h24 e₁ h₁Q) hua hub hab h₁a hfb
  have h₂f := high24_distinct_branches_ne G hΔ e₂ f (h24 e₂ h₂Q) hua hub hab h₂a hfb
  have hxy₁ := high24_external_conflict_adj G hΔ e₁ f hx₁ hy
    (h24 e₁ h₁Q) (h24 f hfQ) hua hub hab hx₁u hyu (hQ h₁Q hfQ h₁f)
  have hxy₂ := high24_external_conflict_adj G hΔ e₂ f hx₂ hy
    (h24 e₂ h₂Q) (h24 f hfQ) hua hub hab hx₂u hyu (hQ h₂Q hfQ h₂f)
  have hx₂₁ : x₂ ≠ x₁ := by
    intro h
    apply hne
    apply Subtype.ext
    rw [h] at hx₂
    exact hx₁.trans hx₂.symm
  have hya : y ≠ a := by
    intro h
    exact high24_edge_not_between_neighbors G hΔ f
      (by simpa only [h] using hy) (h24 f hfQ) hub hua
  have hax₂ : G.Adj a x₂ := G.mem_edgeSet.mp (hx₂ ▸ e₂.property)
  exact no_cross_edge_of_degree_eq_24 G hΔ e₁ hx₁ (h24 e₁ h₁Q)
    (mem_erase.mpr ⟨hx₂₁, (G.mem_neighborFinset a x₂).mpr hax₂⟩)
    (mem_erase.mpr ⟨hya, (G.mem_neighborFinset x₁ y).mpr hxy₁⟩) hxy₂

omit [DecidableRel (conflictGraph G).Adj] in
theorem branchEdges_card_le_three (hΔ : ∀ x, G.degree x ≤ 4)
    (Q : Finset G.edgeSet) {u a : V} (hua : G.Adj u a) :
    (branchEdges G Q u a).card ≤ 3 := by
  classical
  have hs : (branchEdges G Q u a).map (Function.Embedding.subtype _) ⊆
      (G.incidenceFinset a).erase s(a, u) := by
    intro e hemap
    obtain ⟨e, hebranch, rfl⟩ := mem_map.mp hemap
    obtain ⟨_, ha, hu⟩ := (mem_branchEdges G Q u a e).mp hebranch
    refine mem_erase.mpr ⟨?_, G.mem_incidenceFinset.mpr ⟨e.property, ha⟩⟩
    intro heq
    change e.val = s(a, u) at heq
    apply hu
    rw [heq]
    exact Sym2.mem_mk_right _ _
  have hc := card_le_card hs
  have hm : s(a, u) ∈ G.incidenceFinset a :=
    G.mem_incidenceFinset.mpr ⟨hua.symm, Sym2.mem_mk_left _ _⟩
  have he := card_erase_add_one hm
  have hd := hΔ a
  simp only [card_map, SimpleGraph.card_incidenceFinset_eq_degree] at hc he
  omega

/-- At most three occupied branches, each of capacity three, contribute at
most three edges in total: a branch with two edges excludes all others. -/
theorem high24_branch_union_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, (conflictGraph G).degree e = 24)
    (u : V) (A : Finset V) (hA : A.card ≤ 3)
    (hAu : ∀ a ∈ A, G.Adj u a) :
    (A.biUnion (branchEdges G Q u)).card ≤ 3 := by
  classical
  by_cases hbig : ∃ a ∈ A, 1 < (branchEdges G Q u a).card
  · obtain ⟨a, ha, hbig⟩ := hbig
    obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := one_lt_card.mp hbig
    have hs : A.biUnion (branchEdges G Q u) ⊆ branchEdges G Q u a := by
      intro f hf
      obtain ⟨b, hb, hfb⟩ := mem_biUnion.mp hf
      by_cases hba : b = a
      · simpa only [hba] using hfb
      · exact (high24_mixed_branches_cannot_have_fork G hΔ Q hQ h24
          (hAu a ha) (hAu b hb) (Ne.symm hba) e₁ e₂ f h₁ h₂ hfb hne).elim
    exact (card_le_card hs).trans (branchEdges_card_le_three G hΔ Q (hAu a ha))
  · have hsmall : ∀ a ∈ A, (branchEdges G Q u a).card ≤ 1 := by
      intro a ha
      by_contra hn
      exact hbig ⟨a, ha, by omega⟩
    have hs := sum_le_sum (s := A) hsmall
    simp only [sum_const, smul_eq_mul, mul_one] at hs
    exact (card_biUnion_le.trans hs).trans hA

/-- One side of a fixed original edge has at most three external clique
edges. The fixed edge need not itself belong to the clique. -/
theorem high24_side_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, (conflictGraph G).degree e = 24)
    {u v : V} (huv : G.Adj u v) :
    (((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)).card ≤ 3 := by
  have hcard := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hd := hΔ u
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact high24_branch_union_card_le_three G hΔ Q hQ h24 u _ (by omega)
    (fun a ha => (G.mem_neighborFinset u a).mp (mem_erase.mp ha).2)

/-- An all-high24 clique has at most thirteen original edges. The assumptions
refer only to original maximum degree, full conflicts, and full conflict degree. -/
theorem high24_clique_card_le_thirteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 24 ≤ (conflictGraph G).degree e) : Q.card ≤ 13 := by
  classical
  have heq : ∀ e ∈ Q, (conflictGraph G).degree e = 24 :=
    fun e he => conflict_degree_eq_24_of_ge G hΔ e (h24 e he)
  by_cases hQempty : Q = ∅
  · simp [hQempty]
  obtain ⟨e, heQ⟩ := nonempty_iff_ne_empty.mpr hQempty
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ a : Sym2 V, a = e.val from ⟨e.val, rfl⟩)
  have he' : e.val = s(u, v) := he.symm
  have huv : G.Adj u v := G.mem_edgeSet.mp (he' ▸ e.property)
  let U := branchEdges G Q v u
  let T := branchEdges G Q u v
  let A := ((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)
  let B := ((G.neighborFinset v).erase u).biUnion (branchEdges G Q v)
  have hcover : Q ⊆ insert e ((U ∪ T) ∪ (A ∪ B)) := by
    intro f hf
    by_cases hfe : f = e
    · exact mem_insert.mpr (Or.inl hfe)
    apply mem_insert_of_mem
    by_cases hu : u ∈ f.val
    · have hv : v ∉ f.val := by
        intro hv
        exact hfe (Subtype.ext (((Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩).trans he'.symm))
      exact mem_union_left _ (mem_union_left _ ((mem_branchEdges G Q v u f).mpr ⟨hf, hu, hv⟩))
    by_cases hv : v ∈ f.val
    · exact mem_union_left _ (mem_union_right _ ((mem_branchEdges G Q u v f).mpr ⟨hf, hv, hu⟩))
    obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he' (hQ heQ hf (Ne.symm hfe))
    rcases mem_union.mp hw with hwu | hwv
    · exact mem_union_right _ (mem_union_left _
        (mem_biUnion.mpr ⟨w, hwu, (mem_branchEdges G Q u w f).mpr ⟨hf, hwf, hu⟩⟩))
    · exact mem_union_right _ (mem_union_right _
        (mem_biUnion.mpr ⟨w, hwv, (mem_branchEdges G Q v w f).mpr ⟨hf, hwf, hv⟩⟩))
  have hU : U.card ≤ 3 := branchEdges_card_le_three G hΔ Q huv.symm
  have hT : T.card ≤ 3 := branchEdges_card_le_three G hΔ Q huv
  have hA : A.card ≤ 3 := high24_side_card_le_three G hΔ Q hQ heq huv
  have hB : B.card ≤ 3 := high24_side_card_le_three G hΔ Q hQ heq huv.symm
  have hc := card_le_card hcover
  have hi := card_insert_le e ((U ∪ T) ∪ (A ∪ B))
  have hUT := card_union_le U T
  have hAB := card_union_le A B
  have hAll := card_union_le (U ∪ T) (A ∪ B)
  omega

theorem high24_clique_card_le_fifteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 24 ≤ (conflictGraph G).degree e) : Q.card ≤ 15 :=
  (high24_clique_card_le_thirteen G hΔ Q hQ h24).trans (by omega)

end Se20Part.Legacy
