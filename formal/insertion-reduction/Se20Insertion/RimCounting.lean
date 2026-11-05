import Se20Insertion.CriticalStructure

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def VertexOnTriangle (w : V) : Prop := ∃ a b, G.Adj w a ∧ G.Adj w b ∧ G.Adj a b

theorem nonTriangle_incidence_le_two (hΔ : MaxDegreeFour G) {w : V}
    (ht : VertexOnTriangle G w) : incidenceCount G (nonTriangleEdges G) w ≤ 2 := by
  obtain ⟨a,b,hwa,hwb,hab⟩ := ht
  let e := edge G hwa
  let f := edge G hwb
  have hef : e ≠ f := by
    intro h
    have hv := congrArg Subtype.val h
    have : a = b := by
      have h' : a = b ∨ w = b ∧ a = w := by simpa [e,f,edge] using hv
      exact h'.elim id (fun h => h.2.trans h.1)
    exact hab.ne this
  have he : e ∈ incident G w := by simp [e,edge]
  have hf : f ∈ incident G w := by simp [f,edge]
  have heT : OnTriangle G e := ⟨w,a,b,rfl,hwb,hab⟩
  have hfT : OnTriangle G f := ⟨w,b,a,rfl,hwa,hab.symm⟩
  have hsub : ({e,f} : Finset G.edgeSet) ⊆ (incident G w).filter (OnTriangle G) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [he,hf,heT,hfT]
  have htwo := Finset.card_le_card hsub
  have hparts := Finset.card_filter_add_card_filter_not (s := incident G w) (p := OnTriangle G)
  have heq : (incident G w).filter (fun e => ¬ OnTriangle G e) =
      nonTriangleEdges G ∩ incident G w := by ext e; simp [nonTriangleEdges,and_comm]
  rw [heq,card_incident] at hparts
  have hw := hΔ w
  simp only [Finset.card_pair hef] at htwo
  unfold incidenceCount; omega

/-- Theorem 11.39(3), including the intermediate 13-colouring. -/
theorem all_vertices_triangle (hΔ : MaxDegreeFour G) (ht : ∀ w, VertexOnTriangle G w) :
    ((L2 G).induce (nonTriangleEdges G : Set G.edgeSet)).Colorable 13 ∧ StrongColourable G 20 := by
  have hc : ((L2 G).induce (nonTriangleEdges G : Set G.edgeSet)).Colorable 13 := by
    apply colourable_of_degree_lt _ (by decide)
    intro e
    have hdeg := degree_induce_finset (L2 G) (nonTriangleEdges G) e
    convert_to ((nonTriangleEdges G).filter ((L2 G).Adj e.val)).card < 13
    · congr 1
    obtain ⟨u,v,he⟩ : ∃ u v, e.val.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val.val
    have hbound := conflict_incidence_bound G (nonTriangleEdges G) e.val he
    have hs : (∑ w ∈ rim G u v, incidenceCount G (nonTriangleEdges G) w) ≤
        (rim G u v).card * 2 := by
      calc
        _ ≤ ∑ _w ∈ rim G u v, 2 := Finset.sum_le_sum (fun w _ => nonTriangle_incidence_le_two G hΔ (ht w))
        _ = _ := by simp
    have hr := card_rim_le_six G hΔ (G.mem_edgeSet.mp (he ▸ e.val.2))
    omega
  exact ⟨hc,strongColourable_of_nonTriangle G hΔ (hc.mono (by decide))⟩

def internalEdges (F : Finset G.edgeSet) (R : Finset V) : Finset G.edgeSet :=
  F.filter (fun f => ∀ x ∈ f.val, x ∈ R)

/-- Exact double-counting identity behind 11.40(2). -/
theorem rim_incidence_identity (F : Finset G.edgeSet) (e : G.edgeSet) {u v : V}
    (he : e.val = s(u,v)) :
    (∑ w ∈ rim G u v, incidenceCount G F w) =
      (F.filter ((L2 G).Adj e)).card + (internalEdges G F (rim G u v)).card := by
  let R := rim G u v
  have hs : (∑ w ∈ R, incidenceCount G F w) = ∑ f ∈ F, (R.filter (fun w => w ∈ f.val)).card := by
    have hh := PartialColouring.sum_filter_card_swap R F (fun w f => w ∈ f.val)
    have heq (w : V) : F ∩ incident G w = F.filter (fun f => w ∈ f.val) := by
      ext f; simp
    simpa only [incidenceCount,heq] using hh
  have hcount (f : G.edgeSet) : (R.filter (fun w => w ∈ f.val)).card =
      (if (L2 G).Adj e f then 1 else 0) + (if ∀ x ∈ f.val, x ∈ R then 1 else 0) := by
    have hc : (L2 G).Adj e f ↔ ∃ w ∈ R, w ∈ f.val := by
      have h := Finset.ext_iff.mp (conflicts_eq_rim G e he) f
      simpa [R] using h
    obtain ⟨a,b,hf⟩ : ∃ a b, f.val = s(a,b) := Sym2.ind (fun a b => ⟨a,b,rfl⟩) f.val
    have hab : a ≠ b := (G.mem_edgeSet.mp (hf ▸ f.2)).ne
    have hfilter : R.filter (fun w => w ∈ f.val) =
        (if a ∈ R then {a} else ∅) ∪ (if b ∈ R then {b} else ∅) := by
      ext w; simp only [Finset.mem_filter,hf,Sym2.mem_iff]
      by_cases ha : a ∈ R <;> by_cases hb : b ∈ R <;> simp [ha,hb] <;> aesop
    have hc' : (L2 G).Adj e f ↔ a ∈ R ∨ b ∈ R := by
      rw [hc,hf]; simp only [Sym2.mem_iff]; aesop
    rw [hfilter,hc',hf]
    by_cases ha : a ∈ R <;> by_cases hb : b ∈ R <;> simp [ha,hb,hab,Sym2.mem_iff]
  rw [hs]
  simp_rw [hcount]
  rw [Finset.sum_add_distrib]
  simp only [internalEdges,Finset.card_eq_sum_ones,Finset.sum_filter,R]

theorem critical_rim_deficit (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (hcrit : CriticalSet (L2 G) F) {e : G.edgeSet} (heF : e ∈ F) {u v : V}
    (he : e.val = s(u,v)) :
    20 + (internalEdges G F (rim G u v)).card ≤ ∑ w ∈ rim G u v, incidenceCount G F w := by
  rw [rim_incidence_identity G F e he]
  exact Nat.add_le_add_right (critical_min_degree hcrit heF) _

theorem critical_six_rim_deficit (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (hcrit : CriticalSet (L2 G) F) {e : G.edgeSet} (heF : e ∈ F) {u v : V}
    (he : e.val = s(u,v)) (hR : (rim G u v).card = 6) :
    (∑ w ∈ rim G u v, (4 - incidenceCount G F w)) +
      (internalEdges G F (rim G u v)).card ≤ 4 := by
  have hd := critical_rim_deficit G hΔ hcrit heF he
  have hs : (∑ w ∈ rim G u v, (4 - incidenceCount G F w)) +
      (∑ w ∈ rim G u v, incidenceCount G F w) = 24 := by
    rw [← Finset.sum_add_distrib]
    have heach : ∀ w, 4 - incidenceCount G F w + incidenceCount G F w = 4 := by
      intro w
      have hc : incidenceCount G F w ≤ 4 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by simpa [card_incident] using hΔ w)
      omega
    simp [heach,hR]
  omega

/-- Corollary 11.40(3). -/
theorem critical_rim_at_most_two_triangles (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (hcrit : CriticalSet (L2 G) F) {e : G.edgeSet} (heF : e ∈ F) {u v : V}
    (he : e.val = s(u,v)) :
    ((rim G u v).filter (VertexOnTriangle G)).card ≤ 2 := by
  have hF : F ⊆ nonTriangleEdges G := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,critical_no_triangle G hΔ hcrit f hf⟩
  have hs : ∀ w ∈ rim G u v, incidenceCount G F w +
      (if VertexOnTriangle G w then 2 else 0) ≤ 4 := by
    intro w hw
    by_cases ht : VertexOnTriangle G w
    · have hh : incidenceCount G F w ≤ incidenceCount G (nonTriangleEdges G) w :=
        Finset.card_le_card (Finset.inter_subset_inter_right hF)
      have hh' := nonTriangle_incidence_le_two G hΔ ht
      simp only [if_pos ht]; omega
    · have hh : incidenceCount G F w ≤ 4 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by simpa [card_incident] using hΔ w)
      simpa [ht] using hh
  have hsum := Finset.sum_le_sum hs
  rw [Finset.sum_add_distrib] at hsum
  have hcount : (∑ w ∈ rim G u v, if VertexOnTriangle G w then 2 else 0) =
      2 * ((rim G u v).filter (VertexOnTriangle G)).card := by
    rw [← Finset.sum_filter]; simp [Nat.mul_comm]
  rw [hcount] at hsum
  simp only [Finset.sum_const,smul_eq_mul] at hsum
  have hr := card_rim_le_six G hΔ (G.mem_edgeSet.mp (he ▸ e.2))
  have hd := (critical_min_degree hcrit heF).trans (conflict_incidence_bound G F e he)
  omega

end Se20Insertion
