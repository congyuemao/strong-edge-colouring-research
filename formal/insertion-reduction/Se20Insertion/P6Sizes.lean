import Se20Insertion.P6Geometry

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.P6.Pattern
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : Pattern G)

theorem edge_type_card {i j : Fin 3} (hij : i ≠ j) :
    (P.edgesOf i j).card = (Finset.univ.filter (fun x => P.kind x = i)).card * counts i j := by
  let A := Finset.univ.filter (fun x => P.kind x = i)
  let T := P.edgesOf i j
  have hi (x : V) (hx : x ∈ A) : incidenceCount G T x = counts i j := by
    have hxk : P.kind x = i := (Finset.mem_filter.mp hx).2
    rw [incidence_by_neighbours T
      (fun x y => (P.kind x = i ∧ P.kind y = j) ∨ (P.kind x = j ∧ P.kind y = i))
      (fun x y hxy => P.mem_edgesOf (e := edge G hxy) rfl)]
    simpa [hxk,hij] using P.neighbours x j
  have heach (e : G.edgeSet) (he : e ∈ T) : (A.filter (fun x => x ∈ e.val)).card = 1 := by
    obtain ⟨u,v,hev⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
    rcases (P.mem_edgesOf hev).mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · have hf : A.filter (fun x => x ∈ e.val) = {u} := by
        ext x
        simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,hev,Sym2.mem_iff,Finset.mem_singleton]
        constructor
        · rintro ⟨hk,rfl | rfl⟩
          · rfl
          · exact (hij (hk.symm.trans hv)).elim
        · rintro rfl
          exact ⟨hu,Or.inl rfl⟩
      rw [hf,Finset.card_singleton]
    · have hf : A.filter (fun x => x ∈ e.val) = {v} := by
        ext x
        simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,hev,Sym2.mem_iff,Finset.mem_singleton]
        constructor
        · rintro ⟨hk,rfl | rfl⟩
          · exact (hij (hk.symm.trans hu)).elim
          · rfl
        · rintro rfl
          exact ⟨hv,Or.inr rfl⟩
      rw [hf,Finset.card_singleton]
  have heq (x : V) : incidenceCount G T x = (T.filter (fun e => x ∈ e.val)).card := by
    unfold incidenceCount
    congr 1
    ext e
    simp
  have hs := PartialColouring.sum_filter_card_swap A T (fun x e => x ∈ e.val)
  simp_rw [← heq] at hs
  have hl : (∑ x ∈ A, incidenceCount G T x) = A.card * counts i j := by
    rw [Finset.sum_congr rfl hi]
    simp
  have hr : (∑ e ∈ T, (A.filter (fun x => x ∈ e.val)).card) = T.card := by
    rw [Finset.sum_congr rfl heach]
    simp
  rw [hl,hr] at hs
  exact hs.symm

theorem outside_card (t : ℕ)
    (hC : (Finset.univ.filter (fun x => P.kind x = 0)).card = t)
    (hL : (Finset.univ.filter (fun x => P.kind x = 1)).card = 2*t) :
    P.outside.card = 8*t := by
  have hcu := P.edge_type_card (i := 0) (j := 2) (by decide)
  have hlu := P.edge_type_card (i := 1) (j := 2) (by decide)
  rw [hC] at hcu
  rw [hL] at hlu
  have hd : Disjoint (P.edgesOf 0 2) (P.edgesOf 1 2) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    have hn : s((0 : Fin 3),2) ≠ s(1,2) := by decide
    exact hn (he'.symm.trans hf')
  rw [P.outside_eq,Finset.card_union_of_disjoint hd,hcu,hlu]
  simp [counts]
  omega

end Se20Insertion.P6.Pattern

namespace Se20Insertion.P6

variable {I : Type*} [Fintype I] (B : Leaf I → Leaf I → Prop) (hB : ThreeRegular B)

theorem constructed_outside_card : (pattern B hB).outside.card = 8 * Fintype.card I := by
  apply Pattern.outside_card
  · exact (part_card (I := I) 0).trans (by simp)
  · exact (part_card (I := I) 1).trans (by simp)

theorem constructed_edge_counts :
    ((pattern B hB).edgesOf 0 1).card = 2 * Fintype.card I ∧
    ((pattern B hB).edgesOf 0 2).card = 2 * Fintype.card I ∧
    ((pattern B hB).edgesOf 1 2).card = 6 * Fintype.card I := by
  have h01 := (pattern B hB).edge_type_card (i := 0) (j := 1) (by decide)
  have h02 := (pattern B hB).edge_type_card (i := 0) (j := 2) (by decide)
  have h12 := (pattern B hB).edge_type_card (i := 1) (j := 2) (by decide)
  change _ = (Finset.univ.filter (fun x : Vertex I => kind x = 0)).card * _ at h01 h02
  change _ = (Finset.univ.filter (fun x : Vertex I => kind x = 1)).card * _ at h12
  rw [part_card] at h01 h02 h12
  simp [counts] at h01 h02 h12
  omega

end Se20Insertion.P6
