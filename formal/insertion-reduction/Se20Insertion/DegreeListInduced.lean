import Se20Insertion.NonseparatingPair

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.DegreeList
variable {W C : Type*} [Fintype W] [DecidableEq W] [Nonempty C] (H : SimpleGraph W)

/-- Colour towards any nonempty retained induced set. Only vertices outside
the retained set are coloured, and every one has an uncoloured neighbour
when it is removed by the greedy induction. -/
theorem colourable_outside (L : W → Finset C) (hconn : H.Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (S : Finset W) (hne : S.Nonempty) :
    ColourableOn H L (Finset.univ \ S) := by
  apply colourable_of_degenerate H L
  intro T hT ht
  by_contra! hn
  have closed : ∀ x ∈ T, ∀ y, H.Adj x y → y ∈ T := by
    intro x hx y hxy
    have hsub : T.filter (H.Adj x) ⊆ H.neighborFinset x := by
      intro z hz
      exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hz).2
    have heq : T.filter (H.Adj x) = H.neighborFinset x :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact (hd x).trans (hn x hx))
    exact (Finset.mem_filter.mp (heq ▸ ((H.mem_neighborFinset x y).mpr hxy))).1
  obtain ⟨x,hx⟩ := ht
  obtain ⟨r,hr⟩ := hne
  obtain ⟨p⟩ := hconn x r
  have go : ∀ {a b : W}, H.Walk a b → a ∈ T → b ∈ T := by
    intro a b q
    induction q with
    | nil => exact id
    | @cons a b c hab q ih => exact fun ha => ih (closed a ha b hab)
  exact (Finset.mem_sdiff.mp (hT (go p hx))).2 hr

/-- Bad degree lists restrict to bad degree lists on every nonempty induced
set after colouring its complement. This is the reduction to individual
blocks; it does not assume a block decomposition or a classification. -/
theorem bad_induced_lists (L : W → Finset C) (hconn : H.Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ)
    (S : Finset W) (hne : S.Nonempty) :
    ∃ L' : W → Finset C,
      (∀ x ∈ S, (S.filter (H.Adj x)).card ≤ (L' x).card) ∧ ¬ ColourableOn H L' S := by
  obtain ⟨c,hc,hproper⟩ := colourable_outside H L hconn hd S hne
  let N (x : W) := (Finset.univ \ S).filter (H.Adj x)
  let L' (x : W) := L x \ (N x).image c
  refine ⟨L',?_,?_⟩
  · intro x _
    have hs : N x = H.neighborFinset x \ S := by
      ext y
      simp [N]
      tauto
    have hi : S.filter (H.Adj x) = H.neighborFinset x ∩ S := by
      ext y
      simp
      tauto
    have hp := Finset.card_sdiff_add_card_inter (H.neighborFinset x) S
    rw [← hs,← hi,SimpleGraph.card_neighborFinset_eq_degree] at hp
    have hl := Finset.card_sdiff_add_card_inter (L x) ((N x).image c)
    have hb : (L x ∩ (N x).image c).card ≤ (N x).card :=
      (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_image_le
    have hdx := hd x
    change (S.filter (H.Adj x)).card ≤ (L x \ (N x).image c).card
    omega
  · rintro ⟨d,hd,hp⟩
    apply hbad
    refine ⟨fun x => if x ∈ S then d x else c x,?_,?_⟩
    · intro x _
      by_cases hx : x ∈ S
      · simpa [hx] using (Finset.mem_sdiff.mp (hd x hx)).1
      · simpa [hx] using hc x (by simp [hx])
    · intro x _ y _ hxy heq
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
      · exact hp x hx y hy hxy (by simpa [hx,hy] using heq)
      · exact (Finset.mem_sdiff.mp (hd x hx)).2
          (Finset.mem_image.mpr ⟨y,by simp [N,hy,hxy],by simpa [hx,hy] using heq.symm⟩)
      · exact (Finset.mem_sdiff.mp (hd y hy)).2
          (Finset.mem_image.mpr ⟨x,by simp [N,hx,hxy.symm],by simpa [hx,hy] using heq⟩)
      · exact hproper x (by simp [hx]) y (by simp [hy]) hxy (by simpa [hx,hy] using heq)

end Se20Insertion.DegreeList
