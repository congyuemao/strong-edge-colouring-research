import Se20Insertion.P6Construction

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.P6.Pattern
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : Pattern G)

def edgesOf (i j : Fin 3) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => Sym2.map P.kind e.val = s(i,j))

def outside : Finset G.edgeSet := Finset.univ \ P.edgesOf 0 1

theorem mem_edgesOf {i j : Fin 3} {e : G.edgeSet} {x y : V} (he : e.val = s(x,y)) :
    e ∈ P.edgesOf i j ↔ (P.kind x = i ∧ P.kind y = j) ∨ (P.kind x = j ∧ P.kind y = i) := by
  simp [edgesOf,he,Sym2.eq_iff]

theorem incidence_by_neighbours (T : Finset G.edgeSet) (r : V → V → Prop)
    (hr : ∀ x y (hxy : G.Adj x y), edge G hxy ∈ T ↔ r x y) (x : V) :
    incidenceCount G T x = ((G.neighborFinset x).filter (r x)).card := by
  let other (e : G.edgeSet) (he : e ∈ T ∩ incident G x) :=
    Sym2.Mem.other ((mem_incident G x e).mp (Finset.mem_inter.mp he).2)
  have spec (e : G.edgeSet) (he : e ∈ T ∩ incident G x) : s(x,other e he) = e.val :=
    Sym2.other_spec _
  unfold incidenceCount
  apply Finset.card_bij other
  · intro e he
    have ha : G.Adj x (other e he) := G.mem_edgeSet.mp ((spec e he).symm ▸ e.prop)
    refine Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, (hr x _ ha).mp ?_⟩
    have heq : edge G ha = e := Subtype.ext (spec e he)
    rw [heq]
    exact (Finset.mem_inter.mp he).1
  · intro e he f hf hh
    apply Subtype.ext
    exact (spec e he).symm.trans ((congrArg (fun y => s(x,y)) hh).trans (spec f hf))
  · intro y hy
    obtain ⟨hy,hrxy⟩ := Finset.mem_filter.mp hy
    have ha := (G.mem_neighborFinset _ _).mp hy
    have he : edge G ha ∈ T ∩ incident G x :=
      Finset.mem_inter.mpr ⟨(hr x y ha).mpr hrxy,by simp [edge]⟩
    refine ⟨edge G ha,he,?_⟩
    have hh := spec (edge G ha) he
    have hh' : other (edge G ha) he = y ∨ x = y ∧ other (edge G ha) he = x := by
      simpa [edge] using hh
    exact hh'.elim id (fun h => (ha.ne h.1).elim)

def weight : Fin 3 → ℕ := ![2,1,0]
def neighbourWeight : Fin 3 → ℕ := ![2,2,5]

theorem cl_incidence (x : V) : incidenceCount G (P.edgesOf 0 1) x = weight (P.kind x) := by
  rw [incidence_by_neighbours (P.edgesOf 0 1)
    (fun x y => (P.kind x = 0 ∧ P.kind y = 1) ∨ (P.kind x = 1 ∧ P.kind y = 0))
    (fun x y hxy => P.mem_edgesOf (e := edge G hxy) rfl)]
  have h0 := P.neighbours x 0
  have h1 := P.neighbours x 1
  generalize hk : P.kind x = k at *
  fin_cases k <;> simp_all [weight,counts]

theorem neighbour_weight (x : V) :
    (∑ y ∈ G.neighborFinset x, weight (P.kind y)) = neighbourWeight (P.kind x) := by
  have hs : (∑ y ∈ G.neighborFinset x, weight (P.kind y)) =
      ∑ i : Fin 3, ((G.neighborFinset x).filter (fun y => P.kind y = i)).card * weight i := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp
  rw [hs]
  simp_rw [P.neighbours]
  generalize P.kind x = k
  fin_cases k <;> decide

theorem rim_no_edges (hg : 7 ≤ G.egirth) {u v : V} (huv : G.Adj u v)
    {w z : V} (hw : w ∈ rim G u v) (hz : z ∈ rim G u v) : ¬ G.Adj w z := by
  rcases Finset.mem_union.mp hw with hw | hw <;> rcases Finset.mem_union.mp hz with hz | hz
  · exact fun h => GirthGeometry.no_triangle hg
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm
  · intro h
    have hs := GirthGeometry.square_backtrack hg
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm huv.symm
    exact hs.elim (fun h => (Finset.mem_erase.mp hz).1 h.symm) (Finset.mem_erase.mp hw).1
  · intro h
    have hs := GirthGeometry.square_backtrack hg
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm huv
    exact hs.elim (fun h => (Finset.mem_erase.mp hz).1 h.symm) (Finset.mem_erase.mp hw).1
  · exact fun h => GirthGeometry.no_triangle hg
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2) h
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2).symm

/-- Exact selected-edge conflict count; triangle and square exclusions remove all overlaps. -/
theorem cl_conflicts_identity (hg : 7 ≤ G.egirth) (e : G.edgeSet) {u v : V}
    (he : e.val = s(u,v)) :
    ((P.edgesOf 0 1).filter ((L2 G).Adj e)).card + weight (P.kind u) + weight (P.kind v) =
      neighbourWeight (P.kind u) + neighbourWeight (P.kind v) := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  have hint : internalEdges G (P.edgesOf 0 1) (rim G u v) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hh := (Finset.mem_filter.mp hf).2
    obtain ⟨x,y,hfxy⟩ : ∃ x y, f.val = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) f.val
    exact rim_no_edges hg huv (hh x (by simp [hfxy])) (hh y (by simp [hfxy]))
      (G.mem_edgeSet.mp (hfxy ▸ f.prop))
  have hr := rim_incidence_identity G (P.edgesOf 0 1) e he
  rw [hint, Finset.card_empty, Nat.add_zero] at hr
  simp_rw [P.cl_incidence] at hr
  have hd : Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact GirthGeometry.no_triangle hg huv
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hy).2)
      ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hx).2).symm
  rw [rim, Finset.sum_union hd] at hr
  have hu := Finset.sum_erase_add (G.neighborFinset u) (fun x => weight (P.kind x))
    ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.sum_erase_add (G.neighborFinset v) (fun x => weight (P.kind x))
    ((G.mem_neighborFinset _ _).mpr huv.symm)
  rw [P.neighbour_weight] at hu hv
  omega

theorem cl_conflicts_cu (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 0 2) :
    ((P.edgesOf 0 1).filter ((L2 G).Adj e)).card = 5 := by
  obtain ⟨u,v,hev⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hi := P.cl_conflicts_identity hg e hev
  rcases (P.mem_edgesOf hev).mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;>
    simp [hu,hv,weight,neighbourWeight] at hi <;> omega

theorem cl_conflicts_lu (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 1 2) :
    ((P.edgesOf 0 1).filter ((L2 G).Adj e)).card = 6 := by
  obtain ⟨u,v,hev⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hi := P.cl_conflicts_identity hg e hev
  rcases (P.mem_edgesOf hev).mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;>
    simp [hu,hv,weight,neighbourWeight] at hi <;> omega

theorem cl_conflicts_cl (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 0 1) :
    ((P.edgesOf 0 1).filter ((L2 G).Adj e)).card = 1 := by
  obtain ⟨u,v,hev⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hi := P.cl_conflicts_identity hg e hev
  rcases (P.mem_edgesOf hev).mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;>
    simp [hu,hv,weight,neighbourWeight] at hi <;> omega

theorem outside_eq : P.outside = P.edgesOf 0 2 ∪ P.edgesOf 1 2 := by
  ext e
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hn := P.adjacent_different (G.mem_edgeSet.mp (he ▸ e.prop))
  simp only [outside,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,P.mem_edgesOf he]
  generalize P.kind u = i at *
  generalize P.kind v = j at *
  fin_cases i <;> fin_cases j <;> simp_all

theorem outside_degree (hg : 7 ≤ G.egirth) (e : G.edgeSet) :
    ((P.outside).filter ((L2 G).Adj e)).card +
      ((P.edgesOf 0 1).filter ((L2 G).Adj e)).card = 24 := by
  have he : (P.outside).filter ((L2 G).Adj e) = conflicts G e \ P.edgesOf 0 1 := by
    ext f; simp [outside]; tauto
  have hi : (P.edgesOf 0 1).filter ((L2 G).Adj e) = conflicts G e ∩ P.edgesOf 0 1 := by
    ext f; simp; tauto
  rw [he,hi,Finset.card_sdiff_add_card_inter,regular_girth_conflicts_card G P.degree hg]

end Se20Insertion.P6.Pattern
