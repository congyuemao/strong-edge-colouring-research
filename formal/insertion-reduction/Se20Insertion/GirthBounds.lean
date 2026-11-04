import Se20Insertion.GirthGeometry

noncomputable section
open scoped Classical
namespace Se20Insertion.GirthGeometry
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def side (a b : V) : Finset G.edgeSet :=
  ((G.neighborFinset a).erase b).biUnion (incident G)

theorem card_incident_erase_le_three (hΔ : MaxDegreeFour G) (f : G.edgeSet)
    {a : V} (ha : a ∈ f.val) : ((incident G a).erase f).card ≤ 3 := by
  have hh := Finset.card_erase_add_one ((mem_incident G a f).mpr ha)
  have hd : (incident G a).card ≤ 4 := by simpa [card_incident] using hΔ a
  omega

theorem card_side_le_twelve (hΔ : MaxDegreeFour G) {a b : V} (hab : G.Adj a b) :
    (side G a b).card ≤ 12 := by
  have hn := Finset.card_erase_add_one ((G.mem_neighborFinset a b).mpr hab)
  have hd := hΔ a
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
  calc
    _ ≤ ∑ z ∈ (G.neighborFinset a).erase b, (incident G z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ (G.neighborFinset a).erase b, 4 :=
      Finset.sum_le_sum (fun z _ => by simpa [card_incident] using hΔ z)
    _ ≤ 12 := by simp only [Finset.sum_const, smul_eq_mul]; omega

theorem mem_side_of_endpoint {f z : G.edgeSet} {a b : V}
    (hf : f.val = s(a,b)) (hz : a ∈ z.val) (hne : z ≠ f) : z ∈ side G a b := by
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hz
  have hax : G.Adj a x := G.mem_edgeSet.mp (hx ▸ z.2)
  have hxb : x ≠ b := by
    intro h; subst x
    exact hne (Subtype.ext (hx.trans hf.symm))
  exact Finset.mem_biUnion.mpr ⟨x, by simp [hxb, hax], by simp [hx]⟩

theorem common_near_cover (hg : 7 ≤ G.egirth) {f w z : G.edgeSet} {a b c : V}
    (hf : f.val = s(a,b)) (hw : w.val = s(a,c)) (hfw : f ≠ w)
    (hfz : (L2 G).Adj f z) (hwz : w = z ∨ (L2 G).Adj w z) :
    z ∈ side G a b ∪ (incident G b).erase f := by
  have hab : G.Adj a b := G.mem_edgeSet.mp (hf ▸ f.2)
  have hac : G.Adj a c := G.mem_edgeSet.mp (hw ▸ w.2)
  have hbc : b ≠ c := by intro h; subst c; exact hfw (Subtype.ext (hf.trans hw.symm))
  obtain ⟨x,y,hz⟩ : ∃ x y, z.val = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) z.val
  have hxy : G.Adj x y := G.mem_edgeSet.mp (hz ▸ z.2)
  have hh := common_near_endpoints hg hab hac hbc hxy
    (close_of_conflict hf hz (.inr hfz)) (close_of_conflict hw hz hwz)
  by_cases hb : b ∈ z.val
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hfz.ne.symm, by simpa using hb⟩)
  apply Finset.mem_union_left
  by_cases ha : a ∈ z.val
  · exact mem_side_of_endpoint G hf ha hfz.ne.symm
  have ha' : a ≠ x ∧ a ≠ y := by simpa [hz, Sym2.mem_iff] using ha
  have hb' : b ≠ x ∧ b ≠ y := by simpa [hz, Sym2.mem_iff] using hb
  rcases hh.resolve_left ha'.1 |>.resolve_left ha'.2 |>.resolve_left hb'.1 |>.resolve_left hb'.2 with hx | hy
  · exact Finset.mem_biUnion.mpr ⟨x, by simp [hx, Ne.symm hb'.1], by simp [hz]⟩
  · exact Finset.mem_biUnion.mpr ⟨y, by simp [hy, Ne.symm hb'.2], by simp [hz]⟩

theorem common_near_card (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {f w : G.edgeSet} {a b c : V} (hf : f.val = s(a,b)) (hw : w.val = s(a,c))
    (hfw : f ≠ w) (A : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z ∧ (w = z ∨ (L2 G).Adj w z)) : A.card ≤ 15 := by
  have hsub : A ⊆ side G a b ∪ (incident G b).erase f := by
    intro z hz
    exact common_near_cover G hg hf hw hfw (hA z hz).1 (hA z hz).2
  have h1 := card_side_le_twelve G hΔ (G.mem_edgeSet.mp (hf ▸ f.2))
  have h2 := card_incident_erase_le_three G hΔ f (a := b) (by simp [hf])
  have h3 := Finset.card_union_le (side G a b) ((incident G b).erase f)
  have h4 := Finset.card_le_card hsub
  omega

theorem common_far_card (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {f w : G.edgeSet} (hfw : (L2 G).Adj f w)
    (hdis : ¬ ∃ a, a ∈ f.val ∧ a ∈ w.val) (A : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z ∧ (w = z ∨ (L2 G).Adj w z)) : A.card ≤ 6 := by
  obtain ⟨_, a, ha, c, hc, heq | hac⟩ := hfw
  · exact False.elim (hdis ⟨a, ha, heq ▸ hc⟩)
  obtain ⟨b, hf⟩ := Sym2.mem_iff_exists.mp ha
  obtain ⟨d, hw⟩ := Sym2.mem_iff_exists.mp hc
  have hab : G.Adj a b := G.mem_edgeSet.mp (hf ▸ f.2)
  have hcd : G.Adj c d := G.mem_edgeSet.mp (hw ▸ w.2)
  have hbc : b ≠ c := by intro h; exact hdis ⟨b, by simp [hf], h ▸ hc⟩
  have had : a ≠ d := by intro h; exact hdis ⟨a, ha, by simp [hw, h]⟩
  have hbd : b ≠ d := by intro h; exact hdis ⟨b, by simp [hf], by simp [hw, h]⟩
  let ac := edge G hac
  have hsub : A ⊆ (incident G a).erase f ∪ (incident G c).erase ac := by
    intro z hz
    obtain ⟨x,y,hzxy⟩ : ∃ x y, z.val = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) z.val
    have hh := common_far_endpoints hg hab hac hcd hbc had hbd
      (G.mem_edgeSet.mp (hzxy ▸ z.2))
      (close_of_conflict hf hzxy (.inr (hA z hz).1))
      (close_of_conflict hw hzxy (hA z hz).2)
    have hzmem : a ∈ z.val ∨ c ∈ z.val := by simpa [hzxy, Sym2.mem_iff, or_assoc] using hh
    by_cases haz : a ∈ z.val
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(hA z hz).1.ne.symm, by simpa using haz⟩)
    · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, by simpa using hzmem.resolve_left haz⟩)
      intro h; subst z; exact haz (by simp [ac, edge])
  have h1 := card_incident_erase_le_three G hΔ f ha
  have h2 := card_incident_erase_le_three G hΔ ac (a := c) (by simp [ac, edge])
  have h3 := Finset.card_union_le ((incident G a).erase f) ((incident G c).erase ac)
  have h4 := Finset.card_le_card hsub
  omega

theorem opposite_near_card (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    {f w v : G.edgeSet} {a b c d : V}
    (hf : f.val = s(a,b)) (hw : w.val = s(a,c)) (hv : v.val = s(b,d))
    (hfw : f ≠ w) (hfv : f ≠ v) (A : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z ∧
      (w = z ∨ (L2 G).Adj w z) ∧ (v = z ∨ (L2 G).Adj v z)) : A.card ≤ 6 := by
  have hab : G.Adj a b := G.mem_edgeSet.mp (hf ▸ f.2)
  have hac : G.Adj a c := G.mem_edgeSet.mp (hw ▸ w.2)
  have hbd : G.Adj b d := G.mem_edgeSet.mp (hv ▸ v.2)
  have hbc : b ≠ c := by intro h; subst c; exact hfw (Subtype.ext (hf.trans hw.symm))
  have had : a ≠ d := by intro h; subst d; exact hfv (Subtype.ext (hf.trans (Sym2.eq_swap.trans hv.symm)))
  have hsub : A ⊆ (incident G a).erase f ∪ (incident G b).erase f := by
    intro z hz
    obtain ⟨x,y,hzxy⟩ : ∃ x y, z.val = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) z.val
    have hxy : G.Adj x y := G.mem_edgeSet.mp (hzxy ▸ z.2)
    have h1 := common_near_endpoints hg hab hac hbc hxy
      (close_of_conflict hf hzxy (.inr (hA z hz).1)) (close_of_conflict hw hzxy (hA z hz).2.1)
    have h2 := common_near_endpoints hg hab.symm hbd had hxy
      (close_of_conflict (hf.trans Sym2.eq_swap) hzxy (.inr (hA z hz).1))
      (close_of_conflict hv hzxy (hA z hz).2.2)
    have hh := opposite_near_endpoints hg hab hxy h1 h2
    have hh : a ∈ z.val ∨ b ∈ z.val := by simpa [hzxy, Sym2.mem_iff, or_assoc] using hh
    rcases hh with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(hA z hz).1.ne.symm, by simpa using ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨(hA z hz).1.ne.symm, by simpa using hb⟩)
  have h1 := card_incident_erase_le_three G hΔ f (a := a) (by simp [hf])
  have h2 := card_incident_erase_le_three G hΔ f (a := b) (by simp [hf])
  have h3 := Finset.card_union_le ((incident G a).erase f) ((incident G b).erase f)
  have h4 := Finset.card_le_card hsub
  omega

/-- Local geometric inequality behind Theorem 11.44. `C` consists of members
of `A` whose closed conflict neighbourhood contains all of `A`. The case
`C = ∅` is included explicitly. -/
theorem dominator_bound (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    (f : G.edgeSet) (A C : Finset G.edgeSet)
    (hA : ∀ z ∈ A, (L2 G).Adj f z) (hCA : C ⊆ A)
    (hdom : ∀ w ∈ C, ∀ z ∈ A, w = z ∨ (L2 G).Adj w z) :
    A.card + 3 * C.card ≤ 24 := by
  have hCcard := Finset.card_le_card hCA
  by_cases hsmall : A.card ≤ 6
  · omega
  by_cases hC : C = ∅
  · have hsub : A ⊆ conflicts G f := fun z hz => (mem_conflicts G f z).mpr (hA z hz)
    have hh := (Finset.card_le_card hsub).trans (card_conflicts_le_twentyFour G hΔ f)
    simp only [hC, Finset.card_empty, mul_zero, add_zero]
    exact hh
  have hshare : ∀ w ∈ C, ∃ a, a ∈ f.val ∧ a ∈ w.val := by
    intro w hw
    by_contra hn
    exact hsmall (common_far_card G hΔ hg (hA w (hCA hw)) hn A
      (fun z hz => ⟨hA z hz, hdom w hw z hz⟩))
  obtain ⟨w, hwC⟩ := Finset.nonempty_iff_ne_empty.mpr hC
  obtain ⟨a, haf, haw⟩ := hshare w hwC
  obtain ⟨b, hf⟩ := Sym2.mem_iff_exists.mp haf
  obtain ⟨c, hw⟩ := Sym2.mem_iff_exists.mp haw
  have hfw := (hA w (hCA hwC)).ne
  have h15 := common_near_card G hΔ hg hf hw hfw A
    (fun z hz => ⟨hA z hz, hdom w hwC z hz⟩)
  have hsub : C ⊆ (incident G a).erase f := by
    intro v hvC
    have hfv := (hA v (hCA hvC)).ne
    refine Finset.mem_erase.mpr ⟨hfv.symm, ?_⟩
    apply (mem_incident G a v).mpr
    by_contra hav
    obtain ⟨u, huf, huv⟩ := hshare v hvC
    have hub : u = b := by
      simp only [hf, Sym2.mem_iff] at huf
      exact huf.resolve_left (fun h => hav (h ▸ huv))
    have hbv : b ∈ v.val := hub ▸ huv
    obtain ⟨d, hv⟩ := Sym2.mem_iff_exists.mp hbv
    exact hsmall (opposite_near_card G hΔ hg hf hw hv hfw hfv A
      (fun z hz => ⟨hA z hz, hdom w hwC z hz, hdom v hvC z hz⟩))
  have h3 := (Finset.card_le_card hsub).trans (card_incident_erase_le_three G hΔ f haf)
  omega

end Se20Insertion.GirthGeometry
