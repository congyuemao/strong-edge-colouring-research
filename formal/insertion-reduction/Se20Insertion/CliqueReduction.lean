import Se20Insertion.CliqueBoundary

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

theorem fill_of_list_card (φ : PartialColouring H F) (U : Finset W)
    (hdis : Disjoint F U) (hL : ∀ x ∈ U, U.card ≤ (φ.available x).card) :
    ∃ ψ : PartialColouring H (F ∪ U), ∀ x ∈ F, ψ.colour x = φ.colour x := by
  obtain ⟨c,hinj,hc⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun x : U => φ.available x.val)).mp (by
      intro A
      by_cases hA : A.Nonempty
      · obtain ⟨x,hx⟩ := hA
        have hsub := Finset.card_le_card (Finset.subset_biUnion_of_mem
          (fun x : U => φ.available x.val) hx)
        have ha := Finset.card_le_univ A
        rw [Fintype.card_coe] at ha
        exact ha.trans ((hL x.val x.property).trans hsub)
      · simp_all)
  have hf : ∀ x : U, φ.Free x.val (c x) := fun x => (Finset.mem_filter.mp (hc x)).2
  exact ⟨φ.fillLists U c hinj hf,φ.fillLists_agrees U c hinj hf hdis⟩

end Se20Insertion.PartialColouring
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem boundary_iff (S : Finset V) (e : G.edgeSet) :
    e ∈ boundaryEdges G S ↔ (∃ x ∈ e.val, x ∈ S) ∧ ∃ y ∈ e.val, y ∉ S := by
  constructor
  · intro h; obtain ⟨u,hu,v,hv,he⟩ := (Finset.mem_filter.mp h).2
    exact ⟨⟨u,he ▸ Sym2.mem_mk_left u v,hu⟩,v,he ▸ Sym2.mem_mk_right u v,hv⟩
  · rintro ⟨⟨u,hu,huS⟩,v,hv,hvS⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,huS,v,hvS,
      (Sym2.mem_and_mem_iff (show u ≠ v from fun h => hvS (h ▸ huS))).mp ⟨hu,hv⟩⟩

theorem outside_boundary_partition (S : Finset V) :
    outsideEdges G S ∪ boundaryEdges G S = Finset.univ \ internalEdges G Finset.univ S := by
  ext e
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  simp only [Finset.mem_union,boundary_iff,outsideEdges,internalEdges,Finset.mem_sdiff,
    Finset.mem_filter,Finset.mem_univ,true_and,he,Sym2.mem_iff]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all

theorem clique_internal_triangle {S : Finset V} (hS : CliqueSet G S) (hcard : 3 ≤ S.card)
    {e : G.edgeSet} (he : e ∈ internalEdges G Finset.univ S) : OnTriangle G e := by
  obtain ⟨u,v,hev⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hu := (Finset.mem_filter.mp he).2 u (hev ▸ Sym2.mem_mk_left u v)
  have hv := (Finset.mem_filter.mp he).2 v (hev ▸ Sym2.mem_mk_right u v)
  have hp : ({u,v} : Finset V).card ≤ 2 := by by_cases h : u = v <;> simp [h]
  obtain ⟨w,hw,hwn⟩ := Finset.exists_mem_notMem_of_card_lt_card (show ({u,v} : Finset V).card < S.card by omega)
  have hwu : w ≠ u := fun h => hwn (by simp [h])
  have hwv : w ≠ v := fun h => hwn (by simp [h])
  exact ⟨u,v,w,hev,hS u hu w hw hwu.symm,hS v hv w hw hwv.symm⟩

theorem clique_finish (hΔ : MaxDegreeFour G) {S : Finset V}
    (hS : CliqueSet G S) (hcard : 3 ≤ S.card)
    (hc : Nonempty (PartialColouring (L2 G) (outsideEdges G S ∪ boundaryEdges G S))) :
    StrongColourable G 20 := by
  have hfull := triangle_edges_last G hΔ Finset.univ (internalEdges G Finset.univ S)
    (Finset.subset_univ _) (fun e he => clique_internal_triangle G hS hcard he)
    (by rw [← outside_boundary_partition]; exact hc)
  obtain ⟨φ⟩ := hfull
  exact ⟨SimpleGraph.Coloring.mk φ.colour (fun {e f} hef => φ.proper (Finset.mem_univ _) (Finset.mem_univ _) hef)⟩

/-- 11.41(2): a K4 can be deleted and put back, in the original ambient graph. -/
theorem strongColourable_of_delete_K4 (hΔ : MaxDegreeFour G) {S : Finset V}
    (hS : CliqueSet G S) (hcard : S.card = 4)
    (hc : StrongColourable (G.induce {x | x ∉ S}) 20) : StrongColourable G 20 := by
  obtain ⟨φ⟩ := outside_colouring G S hc
  obtain ⟨ψ,_⟩ := φ.fill_of_list_card (boundaryEdges G S) (boundary_disjoint G S) (by
    intro e he
    have hn := boundary_coloured_conflicts G hΔ hS φ he
    have ha := φ.available_card e
    have hu := boundary_card G hΔ hS
    rw [hcard] at hn hu
    omega)
  exact clique_finish G hΔ hS (by omega) ⟨ψ⟩

theorem counterexample_no_K4 (hΔ : MaxDegreeFour G) (hno : ¬ StrongColourable G 20)
    (hdel : ∀ S : Finset V, S.card = 4 → StrongColourable (G.induce {x | x ∉ S}) 20) :
    ∀ S : Finset V, S.card = 4 → ¬ CliqueSet G S := by
  intro S hcard hS
  exact hno (strongColourable_of_delete_K4 G hΔ hS hcard (hdel S hcard))

/-- 11.41(3--4): six equal five-element lists, fifteen distinct blockers
per boundary edge, and all 5*15 component conditions. -/
theorem triangle_boundary_rigidity (hΔ : MaxDegreeFour G) {S : Finset V}
    (hS : CliqueSet G S) (hcard : S.card = 3) (hno : ¬ StrongColourable G 20)
    (φ : PartialColouring (L2 G) (outsideEdges G S)) :
    (boundaryEdges G S).card = 6 ∧
    (∀ e ∈ boundaryEdges G S, ∀ f ∈ boundaryEdges G S, e ≠ f → (L2 G).Adj e f) ∧
    ∃ L : Finset Colour, L.card = 5 ∧
      (∀ e ∈ boundaryEdges G S, φ.available e = L ∧
        (φ.colouredNeighbours e).card = 15 ∧
        Set.InjOn φ.colour (φ.colouredNeighbours e) ∧
        (φ.colouredNeighbours e).image φ.colour = Finset.univ \ L ∧
        ∀ b ∉ L, ∃! m, φ.Neighbour e b m) ∧
      ∀ a ∈ L, ∀ b ∉ L, ∀ e ∈ boundaryEdges G S, ∀ f ∈ boundaryEdges G S,
        ∀ m n, φ.Neighbour e b m → φ.Neighbour f b n → φ.SameComponent a b m n := by
  let U := boundaryEdges G S
  have hrep : ¬ φ.OneSwapListRepair U := by
    rintro ⟨ψ,_,θ,_⟩
    exact hno (clique_finish G hΔ hS (by omega) ⟨θ⟩)
  have h15 (e : G.edgeSet) (he : e ∈ U) : (φ.colouredNeighbours e).card ≤ 15 := by
    have hh := boundary_coloured_conflicts G hΔ hS φ he
    rw [hcard] at hh; exact hh
  have h5 (e : G.edgeSet) (he : e ∈ U) : 5 ≤ (φ.available e).card := by
    have hh := φ.available_card e; have hh' := h15 e he; omega
  have h6 : U.card = 6 := by
    have hh := boundary_card G hΔ hS
    rw [hcard] at hh
    by_contra hn
    obtain ⟨θ,hθ⟩ := φ.fill_of_list_card U (boundary_disjoint G S) (by
      intro e he; have := h5 e he; change U.card ≤ 6 at hh; omega)
    exact hrep ⟨φ,Or.inl rfl,θ,hθ⟩
  obtain ⟨L,hLc,hlists,htight,hconn⟩ := φ.one_swap_list_rigidity U (boundary_disjoint G S)
    (Finset.card_pos.mp (by omega)) (by simpa only [h6] using h5)
    (by intro e he; have := h15 e he; omega) hrep
  have hLc : L.card = 5 := by omega
  refine ⟨h6,fun e he f hf hne => boundary_pairwise_conflict G hS he hf hne,L,hLc,?_,hconn⟩
  intro e he
  have ht := φ.tight_list_neighbours e (by rw [hlists e he,hLc]; have := h15 e he; omega)
  exact ⟨hlists e he,by have := (htight e he).1; omega,ht.2.1,
    by rw [φ.available_complement,hlists e he],(htight e he).2⟩

end Se20Insertion
