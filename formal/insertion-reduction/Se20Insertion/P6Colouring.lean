import Se20Insertion.P6Core
import Se20Insertion.P6Sizes

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.P6.Pattern
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : Pattern G)

/-- Interchanging L and U preserves the construction. -/
def flip : Pattern G where
  kind x := Equiv.swap (1 : Fin 3) 2 (P.kind x)
  neighbours x i := by
    have he : ((G.neighborFinset x).filter (fun y => Equiv.swap (1 : Fin 3) 2 (P.kind y) = i)) =
        (G.neighborFinset x).filter (fun y => P.kind y = Equiv.swap (1 : Fin 3) 2 i) := by
      ext y
      simp only [Finset.mem_filter,Equiv.swap_apply_eq_iff]
    rw [he,P.neighbours]
    generalize P.kind x = k
    fin_cases k <;> fin_cases i <;> decide

theorem flip_edges_01 : P.flip.edgesOf 0 1 = P.edgesOf 0 2 := by
  ext e
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  rw [P.flip.mem_edgesOf he,P.mem_edgesOf he]
  simp only [flip]
  generalize P.kind u = i
  generalize P.kind v = j
  fin_cases i <;> fin_cases j <;> decide

theorem flip_edges_12 : P.flip.edgesOf 1 2 = P.edgesOf 1 2 := by
  ext e
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  rw [P.flip.mem_edgesOf he,P.mem_edgesOf he]
  simp only [flip]
  generalize P.kind u = i
  generalize P.kind v = j
  fin_cases i <;> fin_cases j <;> decide

theorem cu_conflicts_cu (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 0 2) :
    ((P.edgesOf 0 2).filter ((L2 G).Adj e)).card = 1 := by
  simpa only [P.flip_edges_01] using
    P.flip.cl_conflicts_cl hg (show e ∈ P.flip.edgesOf 0 1 by rwa [P.flip_edges_01])

theorem lu_conflicts_lu (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 1 2) :
    ((P.edgesOf 1 2).filter ((L2 G).Adj e)).card = 12 := by
  have hcl := P.cl_conflicts_lu hg he
  have hcu : ((P.edgesOf 0 2).filter ((L2 G).Adj e)).card = 6 := by
    simpa only [P.flip_edges_01] using
      P.flip.cl_conflicts_lu hg (show e ∈ P.flip.edgesOf 1 2 by rwa [P.flip_edges_12])
  have hd := P.outside_degree hg e
  have hdis : Disjoint ((P.edgesOf 0 2).filter ((L2 G).Adj e))
      ((P.edgesOf 1 2).filter ((L2 G).Adj e)) := by
    apply Finset.disjoint_left.mpr
    intro f hf hg
    have h0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
    have hn : s((0 : Fin 3),2) ≠ s(1,2) := by decide
    exact hn (h0.symm.trans h1)
  rw [P.outside_eq,Finset.filter_union,Finset.card_union_of_disjoint hdis,hcl,hcu] at hd
  omega

/-- A full 17-colouring, with C--L exactly the first two colour classes.
The palettes are 2 + 2 + 13; every conflict is judged in the ambient graph. -/
theorem exists_seventeen_colouring (hg : 7 ≤ G.egirth) :
    ∃ c : G.edgeSet → Fin 17,
      (∀ e f, (L2 G).Adj e f → c e ≠ c f) ∧
      ∀ e, (c e).val < 2 ↔ e ∈ P.edgesOf 0 1 := by
  obtain ⟨c0⟩ := colourable_of_degree_lt ((L2 G).induce (P.edgesOf 0 1 : Set G.edgeSet))
    (k := 2) (by decide) (fun e => by
      convert (degree_induce_finset (L2 G) (P.edgesOf 0 1) e).trans_lt
        (show ((P.edgesOf 0 1).filter ((L2 G).Adj e.val)).card < 2 by
          rw [P.cl_conflicts_cl hg e.prop]; decide))
  obtain ⟨c1⟩ := colourable_of_degree_lt ((L2 G).induce (P.edgesOf 0 2 : Set G.edgeSet))
    (k := 2) (by decide) (fun e => by
      convert (degree_induce_finset (L2 G) (P.edgesOf 0 2) e).trans_lt
        (show ((P.edgesOf 0 2).filter ((L2 G).Adj e.val)).card < 2 by
          rw [P.cu_conflicts_cu hg e.prop]; decide))
  obtain ⟨c2⟩ := colourable_of_degree_lt ((L2 G).induce (P.edgesOf 1 2 : Set G.edgeSet))
    (k := 13) (by decide) (fun e => by
      convert (degree_induce_finset (L2 G) (P.edgesOf 1 2) e).trans_lt
        (show ((P.edgesOf 1 2).filter ((L2 G).Adj e.val)).card < 13 by
          rw [P.lu_conflicts_lu hg e.prop]; decide))
  have hlu (e : G.edgeSet) (h0 : e ∉ P.edgesOf 0 1) (h1 : e ∉ P.edgesOf 0 2) : e ∈ P.edgesOf 1 2 := by
    have ho : e ∈ P.outside := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h0⟩
    rw [P.outside_eq] at ho
    exact (Finset.mem_union.mp ho).resolve_left h1
  let d (e : G.edgeSet) : ℕ :=
    if h0 : e ∈ P.edgesOf 0 1 then (c0 ⟨e,h0⟩).val
    else if h1 : e ∈ P.edgesOf 0 2 then 2 + (c1 ⟨e,h1⟩).val
    else 4 + (c2 ⟨e,hlu e h0 h1⟩).val
  have hd (e : G.edgeSet) : d e < 17 := by
    dsimp [d]
    split_ifs <;> omega
  refine ⟨fun e => ⟨d e,hd e⟩,?_,?_⟩
  · intro e f hef heq
    have heq' : d e = d f := congrArg Fin.val heq
    by_cases he0 : e ∈ P.edgesOf 0 1
    · by_cases hf0 : f ∈ P.edgesOf 0 1
      · exact c0.valid (v := ⟨e,he0⟩) (w := ⟨f,hf0⟩) hef
          (Fin.ext (by simpa [d,he0,hf0] using heq'))
      · by_cases hf1 : f ∈ P.edgesOf 0 2 <;> simp only [d,dite_eq_left he0,dite_eq_right hf0,
          dite_true,dite_false,hf1] at heq' <;> omega
    · by_cases he1 : e ∈ P.edgesOf 0 2
      · by_cases hf0 : f ∈ P.edgesOf 0 1
        · simp only [d,dite_eq_right he0,dite_eq_left he1,dite_eq_left hf0] at heq'; omega
        · by_cases hf1 : f ∈ P.edgesOf 0 2
          · apply c1.valid (v := ⟨e,he1⟩) (w := ⟨f,hf1⟩) hef
            apply Fin.ext
            simpa [d,he0,he1,hf0,hf1] using heq'
          · simp only [d,dite_eq_right he0,dite_eq_left he1,dite_eq_right hf0,dite_eq_right hf1] at heq'; omega
      · by_cases hf0 : f ∈ P.edgesOf 0 1
        · simp only [d,dite_eq_right he0,dite_eq_right he1,dite_eq_left hf0] at heq'; omega
        · by_cases hf1 : f ∈ P.edgesOf 0 2
          · simp only [d,dite_eq_right he0,dite_eq_right he1,dite_eq_right hf0,dite_eq_left hf1] at heq'; omega
          · apply c2.valid (v := ⟨e,hlu e he0 he1⟩) (w := ⟨f,hlu f hf0 hf1⟩) hef
            apply Fin.ext
            simpa [d,he0,he1,hf0,hf1] using heq'
  · intro e
    change d e < 2 ↔ _
    by_cases he0 : e ∈ P.edgesOf 0 1
    · simp [d,he0]; omega
    · by_cases he1 : e ∈ P.edgesOf 0 2 <;> simp [d,he0,he1] <;> omega

include P in
theorem strongColourable_seventeen (hg : 7 ≤ G.egirth) : StrongColourable G 17 := by
  obtain ⟨c,hc,_⟩ := P.exists_seventeen_colouring hg
  exact ⟨SimpleGraph.Coloring.mk c (fun {e f} hef => hc e f hef)⟩

/-- The prescribed one-hole states exist for every outside edge. -/
theorem exists_pair_state (hg : 7 ≤ G.egirth) {h : G.edgeSet} (hh : h ∈ P.outside) :
    ∃ φ : PartialColouring (L2 G) (Finset.univ.erase h), P.PairClasses φ 0 1 := by
  obtain ⟨c,hc,hpal⟩ := P.exists_seventeen_colouring hg
  let φ : PartialColouring (L2 G) (Finset.univ.erase h) :=
    ⟨fun e => ⟨(c e).val,by have := (c e).isLt; omega⟩,
      fun {e f} _ _ hef heq => hc e f hef (Fin.ext (congrArg (fun x : Colour => x.val) heq))⟩
  refine ⟨φ,fun e => ?_⟩
  have hcol : φ.colour e ∈ ({0,1} : Finset Colour) ↔ (c e).val < 2 := by
    simp only [Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
    change (c e).val = 0 ∨ (c e).val = 1 ↔ (c e).val < 2
    omega
  rw [hcol,hpal]
  constructor
  · exact And.right
  · intro he
    refine ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,he⟩
    intro heh
    exact (Finset.mem_sdiff.mp hh).2 (heh ▸ he)

end Se20Insertion.P6.Pattern

namespace Se20Insertion.P6
variable {I : Type*} [Fintype I] (B : Leaf I → Leaf I → Prop) (hB : ThreeRegular B)
local instance : DecidableEq (Vertex I) := fun a b => Classical.propDecidable (a = b)

set_option maxHeartbeats 800000 in
/-- Abstract P6 family: the graph is constructed, the colouring exists, and
the selected core is computed. Girth is a premise on the constructed graph. -/
theorem propositionP6 (hg : 7 ≤ (graph B).egirth)
    {h : (graph B).edgeSet} (hh : h ∈ (pattern B hB).outside) :
    ∃ φ : PartialColouring (L2 (graph B)) (Finset.univ.erase h),
      (pattern B hB).PairClasses φ 0 1 ∧
      φ.colourSetS h {0,1} = (pattern B hB).outside ∧
      φ.colourSetCore h {0,1} = (pattern B hB).outside ∧
      (φ.colourSetCore h {0,1}).card = 8 * Fintype.card I ∧
      h ∈ φ.colourSetCore h {0,1} := by
  obtain ⟨φ,hc⟩ := (pattern B hB).exists_pair_state hg hh
  have hcore := (pattern B hB).pair_core_eq φ (by decide : (0 : Colour) ≠ 1) hc hg
  refine ⟨φ,hc,(pattern B hB).pair_S_eq φ (by decide) hc,hcore,?_,?_⟩
  · rw [hcore,constructed_outside_card B hB]
  · rwa [hcore]

end Se20Insertion.P6
