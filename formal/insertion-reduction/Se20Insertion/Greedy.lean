import Se20Insertion.ConflictBounds
import Se20Insertion.Kempe

noncomputable section
open scoped Classical
namespace Se20Insertion

theorem colourable_of_degree_lt {W : Type*} [Fintype W] (H : SimpleGraph W)
    {k : ℕ} (hk : 0 < k) (hdeg : ∀ x, H.degree x < k) : H.Colorable k := by
  have all : ∀ F : Finset W, ∃ c : W → Fin k,
      ∀ x ∈ F, ∀ y ∈ F, H.Adj x y → c x ≠ c y := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, hk⟩, by simp⟩
    | @insert e F he ih =>
      obtain ⟨c, hc⟩ := ih
      let S := (F.filter (H.Adj e)).image c
      have hS : S.card < (Finset.univ : Finset (Fin k)).card := by
        calc
          S.card ≤ (F.filter (H.Adj e)).card := Finset.card_image_le
          _ ≤ (H.neighborFinset e).card := Finset.card_le_card (by
            intro x hx; simpa using (Finset.mem_filter.mp hx).2)
          _ < k := by simpa using hdeg e
          _ = _ := by simp
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hS
      refine ⟨fun x => if x = e then a else c x, ?_⟩
      intro x hx y hy hxy heq
      by_cases hxe : x = e
      · subst x
        have hye : y ≠ e := hxy.ne.symm
        have hyF := (Finset.mem_insert.mp hy).resolve_left hye
        apply ha
        exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyF, hxy⟩,
          by simpa [hye] using heq.symm⟩
      · have hxF := (Finset.mem_insert.mp hx).resolve_left hxe
        by_cases hye : y = e
        · subst y
          apply ha
          exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxF, hxy.symm⟩,
            by simpa [hxe] using heq⟩
        · exact hc x hxF y ((Finset.mem_insert.mp hy).resolve_left hye) hxy
            (by simpa [hxe, hye] using heq)
  obtain ⟨c, hc⟩ := all Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c (fun {x y} hxy => hc x (Finset.mem_univ _) y (Finset.mem_univ _) hxy)⟩

theorem degree_induce_finset {W : Type*} [Fintype W] (H : SimpleGraph W)
    (F : Finset W) (x : (F : Set W)) :
    (H.induce (F : Set W)).degree x = (F.filter (H.Adj x.val)).card := by
  have himage : ((H.induce (F : Set W)).neighborFinset x).image Subtype.val =
      F.filter (H.Adj x.val) := by
    ext y
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, hz⟩
    · rintro ⟨hy, hxy⟩; exact ⟨⟨y, hy⟩, hxy, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

theorem partialColouring_iff_colourable {W : Type*} (H : SimpleGraph W) (F : Finset W) :
    Nonempty (PartialColouring H F) ↔ (H.induce (F : Set W)).Colorable 20 := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨SimpleGraph.Coloring.mk (fun x => φ.colour x.val) (fun {x y} hxy => φ.proper x.2 y.2 hxy)⟩
  · rintro ⟨c⟩
    refine ⟨⟨fun x => if hx : x ∈ F then c ⟨x, hx⟩ else 0, ?_⟩⟩
    intro x y hx hy hxy
    simpa only [dif_pos hx, dif_pos hy] using c.valid (show (H.induce (F : Set W)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)

/-- A matching has at most six conflicts per edge when ambient maximum degree is four. -/
theorem matching_conflicts_le_six {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (M : Finset G.edgeSet)
    (hM : ∀ v, ∀ e ∈ M, ∀ f ∈ M, v ∈ e.val → v ∈ f.val → e = f)
    (e : G.edgeSet) : (M.filter ((L2 G).Adj e)).card ≤ 6 := by
  obtain ⟨u, v, he⟩ : ∃ u v, e.val = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  have heq : M.filter ((L2 G).Adj e) = (rim G u v).biUnion (fun v => incident G v ∩ M) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨hfM, hef⟩
      have hf : f ∈ (rim G u v).biUnion (incident G) := by
        rw [← conflicts_eq_rim G e he]
        exact (mem_conflicts G _ _).mpr hef
      obtain ⟨x, hx, hxf⟩ := Finset.mem_biUnion.mp hf
      exact ⟨x, hx, hxf, hfM⟩
    · rintro ⟨x, hx, hxf, hfM⟩
      refine ⟨hfM, (mem_conflicts G _ _).mp ?_⟩
      rw [conflicts_eq_rim G e he]
      exact Finset.mem_biUnion.mpr ⟨x, hx, hxf⟩
  have hone : ∀ v, (incident G v ∩ M).card ≤ 1 := by
    intro v
    apply Finset.card_le_one.mpr
    intro e he f hf
    exact hM v e (Finset.mem_inter.mp he).2 f (Finset.mem_inter.mp hf).2
      ((mem_incident G _ _).mp (Finset.mem_inter.mp he).1)
      ((mem_incident G _ _).mp (Finset.mem_inter.mp hf).1)
  rw [heq]
  calc
    _ ≤ ∑ v ∈ rim G u v, (incident G v ∩ M).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ rim G u v, 1 := Finset.sum_le_sum (fun v _ => hone v)
    _ = (rim G u v).card := by simp
    _ ≤ 6 := card_rim_le_six G hΔ huv

theorem matching_seven_colourable {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (M : Finset G.edgeSet)
    (hM : ∀ v, ∀ e ∈ M, ∀ f ∈ M, v ∈ e.val → v ∈ f.val → e = f) :
    ((L2 G).induce (M : Set G.edgeSet)).Colorable 7 := by
  apply colourable_of_degree_lt _ (by decide)
  intro e
  have hd := degree_induce_finset (L2 G) M e
  simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd ⊢
  rw [hd]
  exact Nat.lt_succ_of_le (matching_conflicts_le_six G hΔ M hM e.val)

end Se20Insertion
