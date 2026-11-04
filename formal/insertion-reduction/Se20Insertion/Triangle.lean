import Se20Insertion.Counting

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def edge {u v : V} (h : G.Adj u v) : G.edgeSet := ⟨s(u, v), h⟩

def outer (w u v : V) : Finset G.edgeSet :=
  (G.neighborFinset w \ {u, v}).biUnion
    (fun z => (incident G z).filter (fun f => w ∉ f.val))

@[simp] theorem mem_outer (w u v : V) (f : G.edgeSet) :
    f ∈ outer G w u v ↔
      ∃ z, G.Adj w z ∧ z ≠ u ∧ z ≠ v ∧ z ∈ f.val ∧ w ∉ f.val := by
  simp [outer, Finset.mem_biUnion, and_assoc]

theorem card_outer_le_six (hΔ : MaxDegreeFour G) {u v w : V}
    (huv : u ≠ v) (hwu : G.Adj w u) (hwv : G.Adj w v) :
    (outer G w u v).card ≤ 6 := by
  have hsub : ({u, v} : Finset V) ⊆ G.neighborFinset w := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simpa using hwu
    · simpa using hwv
  have hn : (G.neighborFinset w \ {u, v}).card ≤ 2 := by
    have hh := Finset.card_sdiff_add_card_eq_card hsub
    have hd := hΔ w
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    rw [Finset.card_pair huv] at hh
    omega
  have each : ∀ z ∈ G.neighborFinset w \ {u, v},
      ((incident G z).filter (fun f => w ∉ f.val)).card ≤ 3 := by
    intro z hz
    have hwz : G.Adj w z := by simpa using (Finset.mem_sdiff.mp hz).1
    let f := edge G hwz
    have hfm : f ∈ incident G z := by simp [f, edge]
    have hle : (incident G z).filter (fun f => w ∉ f.val) ⊆ (incident G z).erase f := by
      intro g hg
      refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_filter.mp hg).1⟩
      intro heq
      subst g
      exact (Finset.mem_filter.mp hg).2 (by simp [f, edge])
    have hcard := Finset.card_le_card hle
    have herase := Finset.card_erase_add_one hfm
    have hd : (incident G z).card ≤ 4 := by simpa [card_incident] using hΔ z
    omega
  calc
    (outer G w u v).card ≤ ∑ z ∈ G.neighborFinset w \ {u, v},
        ((incident G z).filter (fun f => w ∉ f.val)).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ G.neighborFinset w \ {u, v}, 3 := Finset.sum_le_sum each
    _ ≤ 6 := by simpa using Nat.mul_le_mul_right 3 hn

/-- A neighbour of `uw` outside the shared outer set is a neighbour of `uv`,
unless it is `uv` itself. No disjointness of `outer` and `conflicts uv` is assumed. -/
theorem side_conflict_in_main {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hvw : G.Adj v w) (f : G.edgeSet) (hfe : f ≠ edge G huv)
    (hf : (L2 G).Adj (edge G huw) f) (hout : f ∉ outer G w u v) :
    (L2 G).Adj (edge G huv) f := by
  have hshare : ∀ x, x ∈ (edge G huv).val → x ∈ f.val → (L2 G).Adj (edge G huv) f :=
    fun x hx hxf => ⟨hfe.symm, x, hx, x, hxf, Or.inl rfl⟩
  have hw : w ∈ f.val → (L2 G).Adj (edge G huv) f :=
    fun hw => ⟨hfe.symm, u, by simp [edge], w, hw, Or.inr huw⟩
  have hmem : f ∈ (rim G u w).biUnion (incident G) := by
    rw [← conflicts_eq_rim G (edge G huw) rfl]
    exact (mem_conflicts G _ _).mpr hf
  obtain ⟨x, hx, hxf⟩ := Finset.mem_biUnion.mp hmem
  have hxf : x ∈ f.val := (mem_incident G x f).mp hxf
  rcases Finset.mem_union.mp hx with hx | hx
  · have hux : G.Adj u x := by simpa using (Finset.mem_erase.mp hx).2
    exact ⟨hfe.symm, u, by simp [edge], x, hxf, Or.inr hux⟩
  · have hwx : G.Adj w x := by simpa using (Finset.mem_erase.mp hx).2
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    by_cases hxv : x = v
    · subst x; exact hshare v (by simp [edge]) hxf
    · by_cases hwf : w ∈ f.val
      · exact hw hwf
      · exact False.elim (hout ((mem_outer G w u v f).mpr ⟨x, hwx, hxu, hxv, hxf, hwf⟩))

theorem side_witness {u v w : V} (huw : G.Adj u w) (f : G.edgeSet)
    (hf : (L2 G).Adj (edge G huw) f) (hout : f ∉ outer G w u v)
    (hfu : u ∉ f.val) (hfv : v ∉ f.val) (hfw : w ∉ f.val) :
    ∃ x, G.Adj u x ∧ x ≠ w ∧ x ∈ f.val := by
  have hmem : f ∈ (rim G u w).biUnion (incident G) := by
    rw [← conflicts_eq_rim G (edge G huw) rfl]
    exact (mem_conflicts G _ _).mpr hf
  obtain ⟨x, hx, hxf⟩ := Finset.mem_biUnion.mp hmem
  have hxf : x ∈ f.val := (mem_incident G x f).mp hxf
  rcases Finset.mem_union.mp hx with hx | hx
  · exact ⟨x, by simpa using (Finset.mem_erase.mp hx).2, (Finset.mem_erase.mp hx).1, hxf⟩
  · have hwx : G.Adj w x := by simpa using (Finset.mem_erase.mp hx).2
    have hxu : x ≠ u := fun h => hfu (h ▸ hxf)
    have hxv : x ≠ v := fun h => hfv (h ▸ hxf)
    exact False.elim (hout ((mem_outer G w u v f).mpr ⟨x, hwx, hxu, hxv, hxf, hfw⟩))

theorem saturated_rim (hΔ : MaxDegreeFour G) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hN : (conflicts G (edge G huv)).card = 20) :
    ((rim G u v : Finset V) : Set V).PairwiseDisjoint (incident G) ∧
      ∀ x, G.Adj u x → G.Adj v x → x = w := by
  have hsize := card_rim_le_five G hΔ huv huw hvw
  have hlower := card_conflicts_le_mul_rim G hΔ (edge G huv) rfl
  have hsizeEq : (rim G u v).card = 5 := by omega
  have hsum : (∑ x ∈ rim G u v, (incident G x).card) ≤ 20 := by
    calc
      _ ≤ ∑ _x ∈ rim G u v, 4 := Finset.sum_le_sum (fun x _ => by simpa [card_incident] using hΔ x)
      _ = 20 := by simp [hsizeEq]
  have hcover := conflicts_eq_rim G (edge G huv) rfl
  have hsumEq : ((rim G u v).biUnion (incident G)).card =
      ∑ x ∈ rim G u v, (incident G x).card := by
    have hle : ((rim G u v).biUnion (incident G)).card ≤
        ∑ x ∈ rim G u v, (incident G x).card := Finset.card_biUnion_le
    rw [← hcover, hN] at hle ⊢
    omega
  refine ⟨disjoint_of_card_biUnion_eq_sum _ _ hsumEq, ?_⟩
  intro x hux hvx
  have hcu := Finset.card_union_add_card_inter ((G.neighborFinset u).erase v)
    ((G.neighborFinset v).erase u)
  have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  have hdu := hΔ u
  have hdv := hΔ v
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdu hdv
  change (((G.neighborFinset u).erase v) ∪ ((G.neighborFinset v).erase u)).card = 5 at hsizeEq
  have hinter : (((G.neighborFinset u).erase v) ∩ ((G.neighborFinset v).erase u)).card ≤ 1 := by omega
  apply Finset.card_le_one.mp hinter
  · simp [hux, hvx, hux.ne.symm, hvx.ne.symm]
  · simp [huw, hvw, huw.ne.symm, hvw.ne.symm]

theorem triangle_local_repair (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) (e : G.edgeSet) (heF : e ∉ F) (ht : OnTriangle G e) :
    (∃ c, φ.Free e c) ∨
      ∃ p f q, φ.Single e p f ∧ q ≠ p ∧ φ.Free f q := by
  by_cases hfree : ∃ c, φ.Free e c
  · exact Or.inl hfree
  right
  have hb : ∀ c, ∃ g, φ.Neighbour e c g := by
    simpa [PartialColouring.Free] using hfree
  obtain ⟨u, v, w, he, huw, hvw⟩ := ht
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  have heedge : e = edge G huv := Subtype.ext he
  subst e
  let e := edge G huv
  let f := edge G huw
  let g := edge G hvw
  let N := conflicts G e
  have ht' : OnTriangle G e := ⟨u, v, w, rfl, huw, hvw⟩
  obtain ⟨hNcard, hNF, hinj⟩ := φ.saturated_twenty N e (fun _ => mem_conflicts G _ _)
    (card_conflicts_triangle_le_twenty G hΔ e ht') hb
  obtain ⟨hdisj, hcommon⟩ := saturated_rim G hΔ huv huw hvw hNcard
  have hef : e ≠ f := by
    intro h
    have hvw' : v = w := Sym2.congr_right.mp (congrArg Subtype.val h)
    exact hvw.ne hvw'
  have heg : e ≠ g := by
    intro h
    have hraw : s(v, u) = s(v, w) := Sym2.eq_swap.trans (congrArg Subtype.val h)
    exact huw.ne (Sym2.congr_right.mp hraw)
  have hfN : f ∈ N := (mem_conflicts G _ _).mpr
    ⟨hef, u, by simp [e, edge], u, by simp [f, edge], Or.inl rfl⟩
  have hgN : g ∈ N := (mem_conflicts G _ _).mpr
    ⟨heg, v, by simp [e, edge], v, by simp [g, edge], Or.inl rfl⟩
  let near := (incident G u ∪ incident G v) ∪ incident G w
  let D := N \ near
  have hnear : near.card ≤ 12 := by
    have h1 := Finset.card_union_le (incident G u) (incident G v)
    have h2 := Finset.card_union_le (incident G u ∪ incident G v) (incident G w)
    have hu : (incident G u).card ≤ 4 := by simpa [card_incident] using hΔ u
    have hv : (incident G v).card ≤ 4 := by simpa [card_incident] using hΔ v
    have hw : (incident G w).card ≤ 4 := by simpa [card_incident] using hΔ w
    dsimp [near]
    omega
  have hD : 8 ≤ D.card := by
    have hparts := Finset.card_sdiff_add_card_inter N near
    have hle := Finset.card_le_card (Finset.inter_subset_right (s₁ := N) (s₂ := near))
    dsimp [D]
    omega
  have houtcard := card_outer_le_six G hΔ huv.ne huw.symm hvw.symm
  have hinjD : Set.InjOn φ.colour D := hinj.mono (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)
  have hnot : ¬ D.image φ.colour ⊆ (outer G w u v).image φ.colour := by
    intro hsub
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinjD] at hc
    have hc' := Finset.card_image_le (s := outer G w u v) (f := φ.colour)
    omega
  obtain ⟨q, hqD, hqout⟩ := Finset.not_subset.mp hnot
  obtain ⟨d, hdD, hdq⟩ := Finset.mem_image.mp hqD
  have hdN : d ∈ N := (Finset.mem_sdiff.mp hdD).1
  have hdn : d ∉ near := (Finset.mem_sdiff.mp hdD).2
  have hdu : u ∉ d.val := fun h => hdn (by simp [near, h])
  have hdv : v ∉ d.val := fun h => hdn (by simp [near, h])
  have hdw : w ∉ d.val := fun h => hdn (by simp [near, h])
  have hqf : q ≠ φ.colour f := by
    intro hq
    have hdf := hinj hdN hfN (hdq.trans hq)
    exact hdu (hdf ▸ (by simp [f, edge]))
  have hqg : q ≠ φ.colour g := by
    intro hq
    have hdg := hinj hdN hgN (hdq.trans hq)
    exact hdv (hdg ▸ (by simp [g, edge]))
  have hsingle : ∀ x ∈ N, φ.Single e (φ.colour x) x := by
    intro x hx
    refine ⟨⟨hNF x hx, (mem_conflicts G _ _).mp hx, rfl⟩, ?_⟩
    intro y hy
    exact hinj ((mem_conflicts G _ _).mpr hy.2.1) hx hy.2.2
  by_cases hf : φ.Free f q
  · exact ⟨φ.colour f, f, q, hsingle f hfN, hqf, hf⟩
  by_cases hg : φ.Free g q
  · exact ⟨φ.colour g, g, q, hsingle g hgN, hqg, hg⟩
  obtain ⟨x, hxF, hfx, hxq⟩ : ∃ x, φ.Neighbour f q x := by simpa [PartialColouring.Free] using hf
  obtain ⟨y, hyF, hgy, hyq⟩ : ∃ y, φ.Neighbour g q y := by simpa [PartialColouring.Free] using hg
  have hxo : x ∉ outer G w u v := fun hx => hqout (Finset.mem_image.mpr ⟨x, hx, hxq⟩)
  have hyo : y ∉ outer G w u v := fun hy => hqout (Finset.mem_image.mpr ⟨y, hy, hyq⟩)
  have heF' : e ∉ F := heF
  have hxe : x ≠ e := fun h => heF' (h ▸ hxF)
  have hye : y ≠ e := fun h => heF' (h ▸ hyF)
  have hxN : x ∈ N := (mem_conflicts G _ _).mpr
    (side_conflict_in_main G huv huw hvw x hxe hfx hxo)
  have hyN : y ∈ N := by
    have h' := side_conflict_in_main G huv.symm hvw huw y
      (by simpa [e, edge, Sym2.eq_swap] using hye) hgy
      (by simpa [outer, Finset.pair_comm] using hyo)
    apply (mem_conflicts G _ _).mpr
    simpa [e, edge, Sym2.eq_swap] using h'
  have hxd : x = d := hinj hxN hdN (hxq.trans hdq.symm)
  have hyd : y = d := hinj hyN hdN (hyq.trans hdq.symm)
  subst x; subst y
  obtain ⟨a, hua, haw, had⟩ := side_witness G huw d hfx hxo hdu hdv hdw
  obtain ⟨b, hvb, hbw, hbd⟩ := side_witness G hvw d hgy
    (by simpa [outer, Finset.pair_comm] using hyo) hdv hdu hdw
  have haS : a ∈ rim G u v := Finset.mem_union_left _ (by
    simp [hua, show a ≠ v from fun h => hdv (h ▸ had)])
  have hbS : b ∈ rim G u v := Finset.mem_union_right _ (by
    simp [hvb, show b ≠ u from fun h => hdu (h ▸ hbd)])
  have hab : a = b := by
    by_contra hab
    exact Finset.disjoint_left.mp (hdisj haS hbS hab) (by simpa using had) (by simpa using hbd)
  subst b
  exact False.elim (haw (hcommon a hua hvb))

end Se20Insertion
