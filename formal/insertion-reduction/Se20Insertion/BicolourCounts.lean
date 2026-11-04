import Se20Insertion.ComponentBounds

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion

namespace ComponentBounds
variable {X : Type*} [Fintype X] (H : SimpleGraph X)

/-- Count induced edges by their two endpoints, without changing ambient
adjacency. -/
theorem induced_edges_card (P : Set X) [DecidablePred P] :
    Nat.card (H.induce P).edgeSet =
      ((Finset.univ : Finset H.edgeSet).filter
        (fun e => e.val.out.1 ∈ P ∧ e.val.out.2 ∈ P)).card := by
  let emb : H.induce P ↪g H := inducedEmbedding H P
  let Q : H.edgeSet → Prop := fun e => e.val.out.1 ∈ P ∧ e.val.out.2 ∈ P
  have hm : ∀ e : (H.induce P).edgeSet, Q (emb.mapEdgeSet e) := by
    intro e
    have hall : ∀ x ∈ (emb.mapEdgeSet e).val, x ∈ P := by
      intro x hx
      obtain ⟨z, _hz, hzx⟩ := Sym2.mem_map.mp hx
      exact hzx ▸ z.prop
    exact ⟨hall _ (Sym2.out_fst_mem _), hall _ (Sym2.out_snd_mem _)⟩
  let f : (H.induce P).edgeSet → {e : H.edgeSet // Q e} := fun e => ⟨emb.mapEdgeSet e, hm e⟩
  have hinj : Function.Injective f := by
    intro e k heq
    exact SimpleGraph.Hom.mapEdgeSet.injective emb.toHom emb.injective (congrArg Subtype.val heq)
  have hsur : Function.Surjective f := by
    rintro ⟨e,he⟩
    let u : P := ⟨e.val.out.1, he.1⟩
    let v : P := ⟨e.val.out.2, he.2⟩
    have huv : (H.induce P).Adj u v := by
      change H.Adj e.val.out.1 e.val.out.2
      apply H.mem_edgeSet.mp
      convert e.prop using 1
      exact e.val.out_eq
    refine ⟨⟨s(u,v), huv⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Sym2.map Subtype.val s(u,v) = e.val
    simpa only [Sym2.map_mk, u, v, Sym2.mk] using e.val.out_eq
  have hh := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsur⟩)
  simpa [Q, Nat.card_eq_fintype_card, Fintype.card_subtype] using hh

end ComponentBounds

theorem colour_pair_vertex_count (c : Colour) :
    (∑ a : Colour, ∑ b : Colour, if a < b ∧ (c = a ∨ c = b) then 1 else 0) = 19 := by
  fin_cases c <;> decide

theorem colour_pair_edge_count (c d : Colour) (hcd : c ≠ d) :
    (∑ a : Colour, ∑ b : Colour,
      if a < b ∧ (c = a ∨ c = b) ∧ (d = a ∨ d = b) then 1 else 0) = 1 := by
  rcases lt_or_gt_of_ne hcd with hlt | hlt
  · have hh : ∀ a b : Colour,
        (a < b ∧ (c = a ∨ c = b) ∧ (d = a ∨ d = b)) ↔ a = c ∧ b = d := by
      intro a b
      constructor
      · rintro ⟨hab, hca | hcb, hda | hdb⟩ <;> subst_vars <;> simp_all
        exact (lt_asymm hab hlt).elim
      · rintro ⟨rfl,rfl⟩
        exact ⟨hlt, .inl rfl, .inr rfl⟩
    simp_rw [hh]
    simp [ite_and]
  · have hh : ∀ a b : Colour,
        (a < b ∧ (c = a ∨ c = b) ∧ (d = a ∨ d = b)) ↔ a = d ∧ b = c := by
      intro a b
      constructor
      · rintro ⟨hab, hca | hcb, hda | hdb⟩ <;> subst_vars <;> simp_all
        exact (lt_asymm hab hlt).elim
      · rintro ⟨rfl,rfl⟩
        exact ⟨hlt, .inr rfl, .inl rfl⟩
    simp_rw [hh]
    simp [ite_and]

theorem sum_pair_filter {X : Type*} (T : Finset X) (P : Colour → Colour → X → Prop)
    [∀ a b, DecidablePred (P a b)] :
    (∑ a : Colour, ∑ b : Colour, if a < b then (T.filter (P a b)).card else 0) =
      ∑ x ∈ T, ∑ a : Colour, ∑ b : Colour, if a < b ∧ P a b x then 1 else 0 := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hh : ∀ a b : Colour,
      (if a < b then ∑ x ∈ T, if P a b x then 1 else 0 else 0) =
        ∑ x ∈ T, if a < b ∧ P a b x then 1 else 0 := by
    intro a b
    by_cases hab : a < b <;> simp [hab]
  simp_rw [hh]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := T)]

namespace PartialColouring
variable {W : Type*} [Fintype W] {H : SimpleGraph W} {F : Finset W}

def smallComponentCount (φ : PartialColouring H F) (k : ℕ) : ℕ :=
  ∑ a : Colour, ∑ b : Colour,
    if a < b then ComponentBounds.smallComponents (φ.KempeGraph a b) k else 0

omit [Fintype W] in
theorem bicoloured_card (φ : PartialColouring H F) (a b : Colour) :
    Nat.card (φ.Bicoloured a b) = (F.filter (fun x => φ.colour x = a ∨ φ.colour x = b)).card := by
  have hh : φ.Bicoloured a b = (↑(F.filter (fun x => φ.colour x = a ∨ φ.colour x = b)) : Set W) := by
    ext x
    simp [Bicoloured]
  rw [hh]
  simp

omit [Fintype W] in
theorem bicoloured_mass (φ : PartialColouring H F) :
    (∑ a : Colour, ∑ b : Colour, if a < b then Nat.card (φ.Bicoloured a b) else 0) = 19 * F.card := by
  simp_rw [φ.bicoloured_card]
  rw [sum_pair_filter]
  simp only [colour_pair_vertex_count, Finset.sum_const, smul_eq_mul]
  omega

def colouredEdges (_φ : PartialColouring H F) : Finset H.edgeSet :=
  Finset.univ.filter (fun e => e.val.out.1 ∈ F ∧ e.val.out.2 ∈ F)

theorem bicoloured_edges (φ : PartialColouring H F) :
    (∑ a : Colour, ∑ b : Colour, if a < b then Nat.card (φ.KempeGraph a b).edgeSet else 0) =
      φ.colouredEdges.card := by
  change (∑ a : Colour, ∑ b : Colour,
    if a < b then Nat.card (H.induce (φ.Bicoloured a b)).edgeSet else 0) = _
  simp_rw [ComponentBounds.induced_edges_card]
  rw [sum_pair_filter]
  simp only [colouredEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hf : e.val.out.1 ∈ F ∧ e.val.out.2 ∈ F
  · have hadj : H.Adj e.val.out.1 e.val.out.2 := by
      apply H.mem_edgeSet.mp
      simpa only [Sym2.mk_fst_out_snd_out] using e.prop
    have hcol := φ.proper hf.1 hf.2 hadj
    simpa only [Bicoloured, Set.mem_ofPred_eq, hf.1, hf.2, true_and, ite_true] using
      colour_pair_edge_count _ _ hcol
  · rcases not_and_or.mp hf with hnot | hnot <;> simp [Bicoloured, hnot]

omit [Fintype W] in
theorem coloured_degree (φ : PartialColouring H F) (v : (F : Set W)) :
    (H.induce (F : Set W)).degree v = (φ.colouredNeighbours v.val).card := by
  let e : (F : Set W) ↪ W := Function.Embedding.subtype (· ∈ (F : Set W))
  have hh : ((H.induce (F : Set W)).neighborFinset v).map e = φ.colouredNeighbours v.val := by
    ext x
    simp [e, colouredNeighbours, and_comm]
  have hc := congrArg Finset.card hh
  simpa only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem coloured_edges_le_twelve (φ : PartialColouring H F)
    (hdegree : ∀ x ∈ F, (φ.colouredNeighbours x).card ≤ 24) :
    φ.colouredEdges.card ≤ 12 * F.card := by
  let J := H.induce (F : Set W)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (F : Set W)))
    (fun v _ => (φ.coloured_degree v).trans_le (hdegree v.val v.prop))
  have hhand := J.sum_degrees_eq_twice_card_edges
  have he : Nat.card J.edgeSet = φ.colouredEdges.card := by
    simpa [J, colouredEdges] using ComponentBounds.induced_edges_card H (F : Set W)
  have he' : J.edgeFinset.card = φ.colouredEdges.card := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using he
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  change (∑ v : (F : Set W), J.degree v) ≤ _ at hsum
  rw [hhand, he'] at hsum
  have hF : Fintype.card (F : Set W) = F.card := by simp
  omega

/-- Lemma 11.16, for any partial colouring of a finite simple conflict graph
whose coloured vertices have at most 24 coloured neighbours. -/
theorem lemma1116 (φ : PartialColouring H F)
    (hdegree : ∀ x ∈ F, (φ.colouredNeighbours x).card ≤ 24) :
    7 * F.card ≤ φ.componentCount := by
  have hp : ∀ a b : Colour,
      (if a < b then Nat.card (φ.Bicoloured a b) else 0) ≤
        (if a < b then Nat.card (φ.KempeGraph a b).edgeSet else 0) +
        (if a < b then Nat.card (φ.KempeGraph a b).ConnectedComponent else 0) := by
    intro a b
    split_ifs with hab
    · exact ComponentBounds.vertices_le_edges_add_components (φ.KempeGraph a b)
    · simp
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Colour))
    (fun a _ => Finset.sum_le_sum (s := (Finset.univ : Finset Colour)) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib] at hh
  rw [φ.bicoloured_mass, φ.bicoloured_edges] at hh
  have he := φ.coloured_edges_le_twelve hdegree
  change 19 * F.card ≤ φ.colouredEdges.card + φ.componentCount at hh
  omega

/-- Across all 190 colour pairs, the weighted count of components of orders
one and two is at least twice the number of coloured vertices. -/
theorem small_components_at_least_twice (φ : PartialColouring H F)
    (hdegree : ∀ x ∈ F, (φ.colouredNeighbours x).card ≤ 24) :
    2 * φ.smallComponentCount 1 + φ.smallComponentCount 2 ≥ 2 * F.card := by
  have hp : ∀ a b : Colour,
      3 * (if a < b then Nat.card (φ.KempeGraph a b).ConnectedComponent else 0) ≤
        (if a < b then Nat.card (φ.Bicoloured a b) else 0) +
        2 * (if a < b then ComponentBounds.smallComponents (φ.KempeGraph a b) 1 else 0) +
        (if a < b then ComponentBounds.smallComponents (φ.KempeGraph a b) 2 else 0) := by
    intro a b
    split_ifs with hab
    · exact ComponentBounds.small_components_mass (φ.KempeGraph a b)
    · simp
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Colour))
    (fun a _ => Finset.sum_le_sum (s := (Finset.univ : Finset Colour)) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [φ.bicoloured_mass] at hh
  change 3 * φ.componentCount ≤ 19 * F.card + 2 * φ.smallComponentCount 1 + φ.smallComponentCount 2 at hh
  have hc := φ.lemma1116 hdegree
  omega

end PartialColouring
end Se20Insertion
