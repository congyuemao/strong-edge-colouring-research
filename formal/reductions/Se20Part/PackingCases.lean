import Se20Part.TightComponents

noncomputable section
open scoped Classical BigOperators
namespace Se20Part

variable {W : Type*} (H : SimpleGraph W) (F : Finset W)

theorem packingRank_le_card : packingRank H F ≤ F.card := by
  apply Finset.sup_le
  intro M hM
  split_ifs
  · exact Finset.card_le_card (Finset.mem_powerset.mp hM)
  · omega

theorem packingRank_eq_zero_iff : packingRank H F = 0 ↔ F = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := independent_le_packingRank H F {x} (by simpa using hx)
      (by intro a ha b hb; simp only [Finset.mem_singleton] at ha hb; subst a; subst b; exact H.irrefl)
    simp [h] at hh
  · rintro rfl
    simp [packingRank]

theorem packingRank_le_one_iff : packingRank H F ≤ 1 ↔
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y → H.Adj x y := by
  constructor
  · intro h x hx y hy hne
    by_contra hn
    have hi : Independent H {x,y} := by
      intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact H.irrefl
      · exact hn
      · exact fun h => hn h.symm
      · exact H.irrefl
    have hh := independent_le_packingRank H F {x,y} (by
      intro a ha; rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hx
      · exact Finset.mem_singleton.mp ha ▸ hy) hi
    simp [hne] at hh
    omega
  · intro h
    apply Finset.sup_le
    intro M hM
    split_ifs with hi
    · apply Finset.card_le_one.mpr
      intro x hx y hy
      by_contra hne
      exact hi x hx y hy (h x (Finset.mem_powerset.mp hM hx)
        y (Finset.mem_powerset.mp hM hy) hne)
    · omega

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def isolateCount : ℕ := (Finset.univ.filter (fun v => G.degree v = 0)).card

theorem edge_bound_remove_isolates (hΔ : MaxDegreeFour G) :
    Fintype.card G.edgeSet ≤ 2 * (Fintype.card V - isolateCount G) := by
  have hs : (∑ v, G.degree v) ≤
      ∑ v, (if G.degree v = 0 then 0 else 4) := by
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hz
    · simp [hz]
    · exact hΔ v
  have he : (∑ v, (if G.degree v = 0 then 0 else 4)) =
      4 * (Fintype.card V - isolateCount G) := by
    have hn : (Finset.univ.filter (fun v => G.degree v ≠ 0)).card =
        Fintype.card V - isolateCount G := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      rfl
    rw [← hn]
    simp only [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp_all
  rw [he, G.sum_degrees_eq_twice_card_edges, ← G.card_edgeSet] at hs
  omega

theorem tight_component_edges_injective :
    Set.InjOn (componentEdges G) (tightComponents G) := by
  intro C hC D hD he
  by_contra hne
  have hd := componentEdges_disjoint G hne
  rw [he, disjoint_self] at hd
  have hh := tight_component_edges_card G hD
  rw [hd] at hh
  simp at hh

theorem tauG_univ : tauG G Finset.univ = 2 * (tightComponents G).card := by
  classical
  unfold tauG Packing.tau
  simp only [tightBlocks, Finset.univ_inter]
  rw [Finset.sum_image]
  · have hp : ∀ C ∈ tightComponents G,
        (componentEdges G C).card - 18 = 2 := by
      intro C hC
      have hh : (componentEdges G C).card = 20 := tight_component_edges_card G hC
      simpa only [Finset.univ_inter, hh] using (show 20-18 = (2 : ℕ) by omega)
    rw [Finset.sum_congr rfl hp]
    simp only [Finset.sum_const, nsmul_eq_mul]
    simp [Nat.mul_comm]
  · exact tight_component_edges_injective G

/-- The complete Joos vertex bound quoted as (5.1), including the two
correction terms. This is a separately named citation hypothesis; it is not
asserted to follow from the earlier restricted `JoosNguyen` hypothesis. -/
def JoosVertexBound : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G →
    Fintype.card V ≤ isolateCount G + (tightComponents G).card +
      9 * packingRank (L2 G) Finset.univ

/-- Item 5.6(1), for every finite graph, including isolated vertices and
arbitrarily many tight components. The only hypothesis is the exact cited
Joos bound, in addition to maximum degree four. -/
theorem full_edge_packing_eighteen (hJoos : JoosVertexBound)
    {V : Type} [Fintype V] (G : SimpleGraph V) (hΔ : MaxDegreeFour G) :
    Fintype.card G.edgeSet ≤ 18 * packingRank (L2 G) Finset.univ + tauG G Finset.univ := by
  have he := edge_bound_remove_isolates G hΔ
  have hj := hJoos V G hΔ
  have hi : isolateCount G ≤ Fintype.card V :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  rw [tauG_univ]
  omega

/-- The finite classification 5.5, as a visible, separate hypothesis. It says
exactly that every strong clique of at least 19 edges lies in a tight component. -/
def StrongCliqueClassification55 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G →
    ∀ F : Finset G.edgeSet, 19 ≤ F.card →
      (∀ e ∈ F, ∀ f ∈ F, e ≠ f → (L2 G).Adj e f) →
      ∃ C ∈ tightComponents G, F ⊆ componentEdges G C

theorem packing_eighteen_rank_zero (F : Finset G.edgeSet)
    (hr : packingRank (L2 G) F = 0) :
    F.card ≤ 18 * packingRank (L2 G) F + tauG G F := by
  have hf := (packingRank_eq_zero_iff (L2 G) F).mp hr
  simp [hf]

theorem packing_eighteen_small_set (F : Finset G.edgeSet) (hf : F.card ≤ 18) :
    F.card ≤ 18 * packingRank (L2 G) F + tauG G F := by
  by_cases hr : packingRank (L2 G) F = 0
  · exact packing_eighteen_rank_zero G F hr
  · omega

theorem tauG_of_subset_tight (F : Finset G.edgeSet) (C : G.ConnectedComponent)
    (hC : C ∈ tightComponents G) (hF : F ⊆ componentEdges G C) :
    tauG G F = F.card - 18 := by
  classical
  unfold tauG Packing.tau
  simp only [tightBlocks]
  rw [Finset.sum_image (tight_component_edges_injective G)]
  letI : DecidableEq G.edgeSet := fun a b => Classical.propDecidable (a = b)
  rw [Finset.sum_eq_single C]
  · have hh : (F ∩ componentEdges G C).card = F.card :=
      congrArg Finset.card (Finset.inter_eq_left.mpr hF)
    exact congrArg (fun n => n-18) hh
  · intro D hD hDC
    have hd := componentEdges_disjoint G (Ne.symm hDC)
    have hfdis : Disjoint F (componentEdges G D) := hd.mono_left hF
    have hh := congrArg Finset.card (Finset.disjoint_iff_inter_eq_empty.mp hfdis)
    change (F ∩ componentEdges G D).card = 0 at hh
    omega
  · exact fun hn => False.elim (hn hC)

/-- Item 5.6(2), with the computational classification 5.5 explicit. -/
theorem packing_eighteen_rank_le_one (h55 : StrongCliqueClassification55)
    {V : Type} [Fintype V] (G : SimpleGraph V) (hΔ : MaxDegreeFour G)
    (F : Finset G.edgeSet) (hr : packingRank (L2 G) F ≤ 1) :
    F.card ≤ 18 * packingRank (L2 G) F + tauG G F := by
  by_cases hf : F.card ≤ 18
  · exact packing_eighteen_small_set G F hf
  have hcl := (packingRank_le_one_iff (L2 G) F).mp hr
  obtain ⟨C,hC,hFC⟩ := h55 V G hΔ F (by omega) hcl
  have hrpos : packingRank (L2 G) F ≠ 0 := by
    intro h
    have := (packingRank_eq_zero_iff (L2 G) F).mp h
    simp [this] at hf
  rw [tauG_of_subset_tight G F C hC hFC]
  omega

end Se20Part
