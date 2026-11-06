import Se20Part.CriticalLists

noncomputable section
open scoped Classical
namespace Se20Part.DegreeList
variable {W C : Type*} [DecidableEq W] [Nonempty C] (H : SimpleGraph W)

def ColourableOn (L : W → Finset C) (S : Finset W) : Prop :=
  ∃ c : W → C, (∀ x ∈ S, c x ∈ L x) ∧
    ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → c x ≠ c y

/-- List-greedy induction on a finite set, with the exact induced degrees. -/
theorem colourable_of_degenerate (L : W → Finset C) (S : Finset W)
    (hd : ∀ T ⊆ S, T.Nonempty → ∃ x ∈ T, (T.filter (H.Adj x)).card < (L x).card) :
    ColourableOn H L S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hn : S.Nonempty
    · obtain ⟨x,hx,hdx⟩ := hd S (Finset.Subset.refl _) hn
      obtain ⟨c,hc,hproper⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
        (fun T hT => hd T (hT.trans (Finset.erase_subset _ _)))
      let B := ((S.erase x).filter (H.Adj x)).image c
      have hB : B.card < (L x).card :=
        (Finset.card_image_le.trans (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))).trans_lt hdx
      obtain ⟨a,ha,haB⟩ := Finset.exists_mem_notMem_of_card_lt_card hB
      refine ⟨fun y => if y = x then a else c y,?_,?_⟩
      · intro y hy
        by_cases hyx : y = x
        · subst y; simpa using ha
        · simpa [hyx] using hc y (Finset.mem_erase.mpr ⟨hyx,hy⟩)
      · intro y hy z hz hyz heq
        by_cases hyx : y = x
        · subst y
          have hzx := hyz.ne.symm
          exact haB (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hzx,hz⟩,hyz⟩,by simpa [hzx] using heq.symm⟩)
        · by_cases hzx : z = x
          · subst z
            exact haB (Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr
              ⟨Finset.mem_erase.mpr ⟨hyx,hy⟩,hyz.symm⟩,by simpa [hyx] using heq⟩)
          · exact hproper y (Finset.mem_erase.mpr ⟨hyx,hy⟩)
              z (Finset.mem_erase.mpr ⟨hzx,hz⟩) hyz (by simpa [hyx,hzx] using heq)
    · have hS := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      exact ⟨fun _ => Classical.choice inferInstance,by simp,by simp⟩

variable [Fintype W]

/-- Connected degree lists are colourable if even one list has slack. -/
theorem colourable_of_one_slack (L : W → Finset C) (hconn : H.Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (r : W) (hr : H.degree r < (L r).card) :
    ColourableOn H L Finset.univ := by
  apply colourable_of_degenerate H L
  intro T _ hT
  by_contra! hn
  have hclosed : ∀ x ∈ T, ∀ y, H.Adj x y → y ∈ T := by
    intro x hx y hxy
    have hsub : T.filter (H.Adj x) ⊆ H.neighborFinset x := by
      intro z hz; exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hz).2
    have heq : T.filter (H.Adj x) = H.neighborFinset x :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact (hd x).trans (hn x hx))
    exact (Finset.mem_filter.mp (heq ▸ ((H.mem_neighborFinset x y).mpr hxy))).1
  obtain ⟨x,hx⟩ := hT
  obtain ⟨p⟩ := hconn x r
  have go : ∀ {a b : W}, H.Walk a b → a ∈ T → b ∈ T := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (hclosed a ha b hab)
  have hrT : r ∈ T := go p hx
  have hle : (T.filter (H.Adj r)).card ≤ H.degree r := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy; exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hy).2
  exact (not_lt_of_ge ((hn r hrT).trans hle)) hr

theorem bad_degree_lists_tight (L : W → Finset C) (hconn : H.Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ) :
    ∀ x, (L x).card = H.degree x := by
  intro x
  have hn : ¬ H.degree x < (L x).card := fun h => hbad (colourable_of_one_slack H L hconn hd x h)
  have := hd x
  omega

end Se20Part.DegreeList
