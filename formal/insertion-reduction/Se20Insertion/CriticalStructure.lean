import Se20Insertion.SwapCriteria

noncomputable section
open scoped Classical
namespace Se20Insertion

def CriticalSet {W : Type*} [DecidableEq W] (H : SimpleGraph W) (F : Finset W) : Prop :=
  ¬ Nonempty (PartialColouring H F) ∧
    ∀ e ∈ F, Nonempty (PartialColouring H (F.erase e))

theorem critical_min_degree {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
    (hcrit : CriticalSet H F) {e : W} (he : e ∈ F) :
    20 ≤ (F.filter (H.Adj e)).card := by
  obtain ⟨φ⟩ := hcrit.2 e he
  by_contra hn
  have hN : φ.colouredNeighbours e = F.filter (H.Adj e) := by
    ext x; simp only [PartialColouring.colouredNeighbours, Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨h.2.ne.symm,h.1⟩,h.2⟩⟩
  have ha := φ.available_card e
  rw [hN] at ha
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < (φ.available e).card by omega)
  have hp := φ.insertFree e c (Finset.mem_filter.mp hc).2
  have hd := Finset.insert_erase he
  exact hcrit.1 ⟨hp.restrict F (by rw [hd])⟩

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def nonTriangleEdges : Finset G.edgeSet := Finset.univ.filter (fun e => ¬ OnTriangle G e)

/-- Theorem 11.39(1). -/
theorem strongColourable_of_nonTriangle (hΔ : MaxDegreeFour G)
    (hc : ((L2 G).induce (nonTriangleEdges G : Set G.edgeSet)).Colorable 20) :
    StrongColourable G 20 := by
  let T := Finset.univ.filter (OnTriangle G)
  have heq : Finset.univ \ T = nonTriangleEdges G := by ext e; simp [T,nonTriangleEdges]
  have hp := (partialColouring_iff_colourable _ _).mpr hc
  rw [← heq] at hp
  obtain ⟨φ⟩ := triangle_edges_last G hΔ Finset.univ T (Finset.subset_univ _)
    (fun e he => (Finset.mem_filter.mp he).2) hp
  exact ⟨SimpleGraph.Coloring.mk φ.colour (fun {e f} hef => φ.proper (by simp) (by simp) hef)⟩

def incidenceCount (F : Finset G.edgeSet) (u : V) : ℕ := (F ∩ incident G u).card

theorem conflict_incidence_bound (F : Finset G.edgeSet) (e : G.edgeSet) {u v : V}
    (he : e.val = s(u,v)) :
    (F.filter ((L2 G).Adj e)).card ≤ ∑ w ∈ rim G u v, incidenceCount G F w := by
  have heq : F.filter ((L2 G).Adj e) =
      (rim G u v).biUnion (fun w => F ∩ incident G w) := by
    ext f
    have hc := Finset.ext_iff.mp (conflicts_eq_rim G e he) f
    simp only [mem_conflicts, Finset.mem_biUnion, mem_incident] at hc
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_inter, mem_incident]
    rw [hc]
    aesop
  rw [heq]
  exact Finset.card_biUnion_le

/-- A finite degeneracy condition, stated directly on all subsets. -/
def DegenerateOn {W : Type*} (H : SimpleGraph W) (F : Finset W) (d : ℕ) : Prop :=
  ∀ S ⊆ F, S.Nonempty → ∃ e ∈ S, (S.filter (H.Adj e)).card ≤ d

theorem partialColouring_of_degenerate {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
    (hd : DegenerateOn H F 19) : Nonempty (PartialColouring H F) := by
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hF : F.Nonempty
    · obtain ⟨e,he,hedeg⟩ := hd F (Finset.Subset.refl _) hF
      obtain ⟨φ⟩ := ih (F.erase e) (Finset.erase_ssubset he)
        (fun S hS hne => hd S (hS.trans (Finset.erase_subset _ _)) hne)
      have hc : (φ.colouredNeighbours e).card ≤ 19 :=
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans hedeg
      have ha := φ.available_card e
      obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < (φ.available e).card by omega)
      have ψ := φ.insertFree e c (Finset.mem_filter.mp hc).2
      exact ⟨ψ.restrict F (by rw [Finset.insert_erase he])⟩
    · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      exact ⟨⟨fun _ => 0, by simp⟩⟩

theorem strongColourable_of_nonTriangle_degenerate (hΔ : MaxDegreeFour G)
    (hd : DegenerateOn (L2 G) (nonTriangleEdges G) 19) : StrongColourable G 20 :=
  strongColourable_of_nonTriangle G hΔ
    ((partialColouring_iff_colourable _ _).mp (partialColouring_of_degenerate hd))

theorem strongColourable_of_rim_sum (hΔ : MaxDegreeFour G)
    (hr : ∀ e ∈ nonTriangleEdges G, ∀ u v, e.val = s(u,v) →
      (∑ w ∈ rim G u v, incidenceCount G (nonTriangleEdges G) w) ≤ 19) :
    StrongColourable G 20 := by
  apply strongColourable_of_nonTriangle_degenerate G hΔ
  intro S hS hne
  obtain ⟨e,he⟩ := hne
  obtain ⟨u,v,huv⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  refine ⟨e,he,?_⟩
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hS)).trans
    ((conflict_incidence_bound G _ e huv).trans (hr e (hS he) u v huv))

theorem critical_no_triangle (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (hcrit : CriticalSet (L2 G) F) : ∀ e ∈ F, ¬ OnTriangle G e := by
  intro e he ht
  obtain ⟨φ⟩ := hcrit.2 e he
  obtain ⟨ψ,_⟩ := triangle_insertion G hΔ φ e (by simp) ht
  exact hcrit.1 ⟨ψ.restrict F (by
    intro x hx
    by_cases hxe : x = e
    · simp [hxe]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxe,hx⟩))⟩

/-- Proposition 11.33 is an explicit hypothesis. -/
def Proposition1133 : Prop :=
  ∀ Q : Finset G.edgeSet, (∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → (L2 G).Adj e f) →
    16 ≤ Q.card → ∃ e ∈ Q, (conflicts G e).card ≤ 19

/-- Corollary 11.34 and item 4 of 11.40, with 11.33 explicit. -/
theorem critical_degree_clique (hΔ : MaxDegreeFour G) (hD : Proposition1133 G)
    {F : Finset G.edgeSet} (hcrit : CriticalSet (L2 G) F) :
    (∀ e ∈ F, 20 ≤ (F.filter ((L2 G).Adj e)).card ∧
      (F.filter ((L2 G).Adj e)).card ≤ 24) ∧
    (∀ Q ⊆ F, (∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → (L2 G).Adj e f) → Q.card ≤ 15) := by
  have hle (e : G.edgeSet) : (F.filter ((L2 G).Adj e)).card ≤ (conflicts G e).card :=
    Finset.card_le_card (by intro f hf; exact (mem_conflicts G e f).mpr (Finset.mem_filter.mp hf).2)
  refine ⟨fun e he => ⟨critical_min_degree hcrit he, (hle e).trans
    (card_conflicts_le_twentyFour G hΔ e)⟩, ?_⟩
  intro Q hQ hcl
  by_contra hn
  obtain ⟨e,he,hd⟩ := hD Q hcl (by omega)
  have := critical_min_degree hcrit (hQ he)
  have := hle e
  omega

/-- Proposition 11.41(1); vertex-minimality supplies the deletion hypothesis. -/
theorem counterexample_vertex_nonTriangle (hΔ : MaxDegreeFour G)
    (hno : ¬ StrongColourable G 20)
    (hdel : ∀ v, StrongColourable (G.induce {x | x ≠ v}) 20) :
    ∀ v, ∃ e ∈ incident G v, ¬ OnTriangle G e := by
  intro v
  by_contra hn
  have ht : ∀ e ∈ incident G v, OnTriangle G e := by
    intro e he
    by_contra h
    exact hn ⟨e,he,h⟩
  obtain ⟨φ⟩ := triangle_edges_last G hΔ Finset.univ (incident G v) (Finset.subset_univ _)
    ht (starColouring_of_deleteColourable G v (hdel v))
  exact hno ⟨SimpleGraph.Coloring.mk φ.colour (fun {e f} hef => φ.proper (by simp) (by simp) hef)⟩

end Se20Insertion
