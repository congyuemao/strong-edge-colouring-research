import Se20Part.PaletteExtension

noncomputable section
open scoped Classical
namespace Se20Part

def HasListColouring {W C : Type*} (H : SimpleGraph W) (L : W → Finset C) : Prop :=
  ∃ c : W → C, (∀ v, c v ∈ L v) ∧ ∀ u v, H.Adj u v → c u ≠ c v

/-- The small-colour-pool lemma used in G14. It applies to arbitrary
finite lists over an arbitrary colour type, without a finite search. -/
theorem small_colour_pool {W C : Type*} [Fintype W] [DecidableEq C]
    (H : SimpleGraph W) (k : ℕ)
    (hsmall : ∀ L : W → Finset C, (∀ v, k ≤ (L v).card) →
      (Finset.univ.biUnion L).card < Fintype.card W → HasListColouring H L)
    (L : W → Finset C) (hL : ∀ v, k ≤ (L v).card) : HasListColouring H L := by
  by_cases hh : ∀ S : Finset W, S.card ≤ (S.biUnion L).card
  · obtain ⟨c,hc,hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hh
    exact ⟨c,hm,fun _ _ h he => h.ne (hc he)⟩
  push_neg at hh
  let bad := (Finset.univ : Finset W).powerset.filter (fun S => (S.biUnion L).card < S.card)
  have hbad : bad.Nonempty := by
    obtain ⟨S,hS⟩ := hh
    exact ⟨S,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hS⟩⟩
  obtain ⟨S,hS,hmax⟩ := bad.exists_max_image Finset.card hbad
  have hdef : (S.biUnion L).card < S.card := (Finset.mem_filter.mp hS).2
  let U := S.biUnion L
  have hUc : U.card < Fintype.card W := hdef.trans_le (Finset.card_le_univ S)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hkU : k ≤ U.card := (hL i).trans (Finset.card_le_card
    (show L i ⊆ U from fun c hc => Finset.mem_biUnion.mpr ⟨i,hi,hc⟩))
  obtain ⟨J,hJU,hJ⟩ := Finset.exists_subset_card_eq hkU
  let L' : W → Finset C := fun v => if v ∈ S then L v else J
  have hL' : ∀ v, k ≤ (L' v).card := by
    intro v; dsimp [L']; split_ifs <;> simp_all
  have hpool : Finset.univ.biUnion L' ⊆ U := by
    intro c hc
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hc
    dsimp [L'] at hv
    split_ifs at hv with hs
    · exact Finset.mem_biUnion.mpr ⟨v,hs,hv⟩
    · exact hJU hv
  obtain ⟨c,hc,hproper⟩ := hsmall L' hL' ((Finset.card_le_card hpool).trans_lt hUc)
  let outside := {v : W // v ∉ S}
  let R : outside → Finset C := fun v => L v.1 \ U
  have hhall : ∀ T : Finset outside, T.card ≤ (T.biUnion R).card := by
    intro T
    by_cases hT : T = ∅
    · simp [hT]
    let T' : Finset W := T.image Subtype.val
    have hTc : T'.card = T.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hdis : Disjoint S T' := by
      apply Finset.disjoint_left.mpr
      intro v hv ht
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ht
      exact w.2 hv
    have hSTc : (S ∪ T').card = S.card + T.card := by
      rw [Finset.card_union_of_disjoint hdis,hTc]
    have hgood : (S ∪ T').card ≤ ((S ∪ T').biUnion L).card := by
      by_contra! hn
      have hm := hmax (S ∪ T') (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hn⟩)
      have htpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
      omega
    have hcover : (S ∪ T').biUnion L ⊆ U ∪ T.biUnion R := by
      intro a ha
      obtain ⟨v,hv,hav⟩ := Finset.mem_biUnion.mp ha
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v,hv,hav⟩)
      · by_cases hau : a ∈ U
        · exact Finset.mem_union_left _ hau
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨w,hw,Finset.mem_sdiff.mpr ⟨hav,hau⟩⟩)
    have hupper := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    change U.card < S.card at hdef
    omega
  obtain ⟨g,hg,hgm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' R).mp hhall
  let f : W → C := fun v => if hv : v ∈ S then c v else g ⟨v,hv⟩
  refine ⟨f,?_,?_⟩
  · intro v
    dsimp [f]; split_ifs with hv
    · simpa [L',hv] using hc v
    · exact (Finset.mem_sdiff.mp (hgm ⟨v,hv⟩)).1
  · intro u v huv
    have hcU : ∀ w ∈ S, c w ∈ U := by
      intro w hw
      exact Finset.mem_biUnion.mpr ⟨w,hw,by simpa [L',hw] using hc w⟩
    dsimp [f]; split_ifs with hu hv hv
    · exact hproper _ _ huv
    · intro he
      exact (Finset.mem_sdiff.mp (hgm ⟨v,hv⟩)).2 (he ▸ hcU u hu)
    · intro he
      exact (Finset.mem_sdiff.mp (hgm ⟨u,hu⟩)).2 (he.symm ▸ hcU v hv)
    · intro he
      exact huv.ne (congrArg Subtype.val (hg he))

end Se20Part
