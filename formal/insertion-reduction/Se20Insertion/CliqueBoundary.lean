import Se20Insertion.StarListRigidity

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def outsideEdges (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => ∀ x ∈ e.val, x ∉ S)

def boundaryEdges (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => ∃ u ∈ S, ∃ v ∉ S, e.val = s(u,v))

def CliqueSet (S : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

theorem outside_colouring (S : Finset V)
    (hc : StrongColourable (G.induce {x | x ∉ S}) 20) :
    Nonempty (PartialColouring (L2 G) (outsideEdges G S)) := by
  obtain ⟨c⟩ := hc
  have ex (e : G.edgeSet) (he : e ∈ outsideEdges G S) :
      ∃ f : (G.induce {x | x ∉ S}).edgeSet, (inducedEmbedding G {x | x ∉ S}).mapEdgeSet f = e :=
    exists_induced_edge G _ e (Finset.mem_filter.mp he).2
  refine ⟨⟨fun e => if he : e ∈ outsideEdges G S then c (ex e he).choose else 0, ?_⟩⟩
  intro e f he hf hef
  simp only [dif_pos he,dif_pos hf]
  apply c.valid
  apply (L2_induce_adj_iff G {x | x ∉ S} _ _).mp
  rw [(ex e he).choose_spec,(ex f hf).choose_spec]
  exact hef

theorem boundary_disjoint (S : Finset V) : Disjoint (outsideEdges G S) (boundaryEdges G S) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨u,hu,v,_,hev⟩ := (Finset.mem_filter.mp hf).2
  exact (Finset.mem_filter.mp he).2 u (hev ▸ Sym2.mem_mk_left u v) hu

theorem boundary_pairwise_conflict {S : Finset V} (hS : CliqueSet G S)
    {e f : G.edgeSet} (he : e ∈ boundaryEdges G S) (hf : f ∈ boundaryEdges G S) (hne : e ≠ f) :
    (L2 G).Adj e f := by
  obtain ⟨u,hu,v,_,hev⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨w,hw,z,_,hfz⟩ := (Finset.mem_filter.mp hf).2
  exact ⟨hne,u,hev ▸ Sym2.mem_mk_left u v,w,hfz ▸ Sym2.mem_mk_left w z,
    if h : u = w then Or.inl h else Or.inr (hS u hu w hw h)⟩

theorem clique_outside_neighbours (hΔ : MaxDegreeFour G) {S : Finset V}
    (hS : CliqueSet G S) {u : V} (hu : u ∈ S) :
    (G.neighborFinset u \ S).card + S.card ≤ 5 := by
  have sub : S.erase u ⊆ G.neighborFinset u ∩ S := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
      (hS u hu v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1.symm), (Finset.mem_erase.mp hv).2⟩
  have hc := Finset.card_le_card sub
  have he := Finset.card_erase_add_one hu
  have hp := Finset.card_sdiff_add_card_inter (G.neighborFinset u) S
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hp
  have hd := hΔ u; omega

theorem boundary_card (hΔ : MaxDegreeFour G) {S : Finset V} (hS : CliqueSet G S) :
    (boundaryEdges G S).card ≤ S.card * (5 - S.card) := by
  let B (u : V) := (incident G u).filter (fun e => ∃ v ∉ S, e.val = s(u,v))
  have heq : boundaryEdges G S = S.biUnion B := by
    ext e
    simp only [boundaryEdges,B,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,mem_incident]
    constructor
    · rintro ⟨u,hu,v,hv,hev⟩; exact ⟨u,hu,hev ▸ Sym2.mem_mk_left u v,v,hv,hev⟩
    · rintro ⟨u,hu,_,v,hv,hev⟩; exact ⟨u,hu,v,hv,hev⟩
  have bcard (u : V) (hu : u ∈ S) : (B u).card ≤ 5 - S.card := by
    have him : B u = ((G.neighborFinset u \ S).attach).image
        (fun v => edge G ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp v.property).1)) := by
      ext e
      simp only [B,Finset.mem_filter,mem_incident,Finset.mem_image,Finset.mem_attach,true_and]
      constructor
      · rintro ⟨_,v,hv,hev⟩
        have huv : G.Adj u v := G.mem_edgeSet.mp (hev ▸ e.2)
        exact ⟨⟨v,Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr huv,hv⟩⟩,Subtype.ext hev.symm⟩
      · rintro ⟨v,rfl⟩
        exact ⟨by simp [edge],v.val,(Finset.mem_sdiff.mp v.property).2,rfl⟩
    rw [him]
    have hl := Finset.card_image_le (s := (G.neighborFinset u \ S).attach)
      (f := fun v => edge G ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp v.property).1))
    rw [Finset.card_attach] at hl
    have := clique_outside_neighbours G hΔ hS hu
    omega
  rw [heq]
  calc
    _ ≤ ∑ u ∈ S, (B u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, (5 - S.card) := Finset.sum_le_sum bcard
    _ = _ := by simp

/-- Uniform ambient count: 15 for a triangle, 12 for K4. -/
theorem boundary_coloured_conflicts (hΔ : MaxDegreeFour G) {S : Finset V}
    (hS : CliqueSet G S) (φ : PartialColouring (L2 G) (outsideEdges G S))
    {e : G.edgeSet} (he : e ∈ boundaryEdges G S) :
    (φ.colouredNeighbours e).card ≤ 3 * (5 - S.card) + 9 := by
  obtain ⟨u,hu,v,hv,hev⟩ := (Finset.mem_filter.mp he).2
  have huv : G.Adj u v := G.mem_edgeSet.mp (hev ▸ e.2)
  let B := (G.neighborFinset u \ S).biUnion (branch G u)
  have hc : B.card ≤ 3 * (5 - S.card) := by
    have hn := clique_outside_neighbours G hΔ hS hu
    calc
      _ ≤ ∑ w ∈ G.neighborFinset u \ S, (branch G u w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ G.neighborFinset u \ S, 3 := Finset.sum_le_sum (fun w hw =>
        branch_card_le G hΔ ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hw).1))
      _ ≤ _ := by simp only [Finset.sum_const,smul_eq_mul]; omega
  have hsub : φ.colouredNeighbours e ⊆ B ∪ shell G u v := by
    intro f hf
    obtain ⟨hfF,hef⟩ := Finset.mem_filter.mp hf
    have out := (Finset.mem_filter.mp hfF).2
    have hm := (mem_conflicts G e f).mpr hef
    rw [conflicts_star_decomposition G e hev] at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact False.elim (out u ((mem_incident G u f).mp (Finset.mem_erase.mp hm).2) hu)
      · obtain ⟨w,hw,hf⟩ := Finset.mem_biUnion.mp hm
        refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w,?_,hf⟩)
        exact Finset.mem_sdiff.mpr ⟨hw,out w ((mem_incident G w f).mp (Finset.mem_sdiff.mp hf).1)⟩
    · exact Finset.mem_union_right _ hm
  have hl := Finset.card_le_card hsub
  have hun := Finset.card_union_le B (shell G u v)
  have hs := shell_card_le G hΔ huv
  omega

end Se20Insertion
