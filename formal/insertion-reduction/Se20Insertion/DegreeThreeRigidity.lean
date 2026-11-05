import Se20Insertion.StarGeometry

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

/-- At most one nonempty component swap, then at most one old vertex recoloured. -/
def SwapSingleRepair (φ : PartialColouring H F) (e : W) : Prop :=
  ∃ ψ : PartialColouring H F, (ψ = φ ∨ φ.OneKempeSwap ψ) ∧
    ∃ θ : PartialColouring H (insert e F),
      (F.filter (fun x => θ.colour x ≠ ψ.colour x)).card ≤ 1

theorem repair_of_free (φ : PartialColouring H F) {e : W} (he : e ∉ F)
    {c : Colour} (hc : φ.Free e c) : φ.SwapSingleRepair e := by
  refine ⟨φ, Or.inl rfl, φ.insertFree e c hc, ?_⟩
  have hz : F.filter (fun x => (φ.insertFree e c hc).colour x ≠ φ.colour x) = ∅ := by
    ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact fun hx => not_not.mpr (φ.insertFree_unchanged he hc x hx)
  simp [hz]

/-- A tight 11+9 cover of all twenty colours forces a complementary nine-colour shell. -/
theorem palette_split (φ : PartialColouring H F) (K S : Finset W)
    (hK : K.card ≤ 11) (hS : S.card ≤ 9)
    (hall : ∀ c : Colour, ∃ x ∈ K ∪ S, x ∈ F ∧ φ.colour x = c) :
    K.card = 11 ∧ S.card = 9 ∧ Disjoint K S ∧
      (∀ x ∈ K ∪ S, x ∈ F) ∧ Set.InjOn φ.colour (↑(K ∪ S) : Set W) ∧
      S.image φ.colour = Finset.univ \ K.image φ.colour := by
  let D := (K ∪ S).filter (· ∈ F)
  have him : D.image φ.colour = Finset.univ := by
    ext c; simp only [Finset.mem_univ, iff_true]
    obtain ⟨x, hx, hxF, hc⟩ := hall c
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,hxF⟩, hc⟩
  have hl := Finset.card_image_le (s := D) (f := φ.colour)
  have hd := Finset.card_filter_le (s := K ∪ S) (p := (· ∈ F))
  change D.card ≤ (K ∪ S).card at hd
  have hu := Finset.card_union_le K S
  have hi := Finset.card_union_add_card_inter K S
  have hc20 : (Finset.univ : Finset Colour).card = 20 := rfl
  rw [him, hc20] at hl
  have hD : D = K ∪ S := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hdis : Disjoint K S := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.card_eq_zero.mp (by omega))
  have hinj : Set.InjOn φ.colour (↑(K ∪ S) : Set W) := by
    apply Finset.card_image_iff.mp
    rw [← hD, him, hc20]; omega
  refine ⟨by omega, by omega, hdis, ?_, hinj, ?_⟩
  · intro x hx; rw [← hD] at hx; exact (Finset.mem_filter.mp hx).2
  · ext c
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨x,hx,hxc⟩ ⟨y,hy,hyc⟩
      have hxy := hinj (Finset.mem_union_right _ hx) (Finset.mem_union_left _ hy) (hxc.trans hyc.symm)
      exact Finset.disjoint_left.mp hdis hy (hxy ▸ hx)
    · intro hn
      obtain ⟨x, hx, _, hxc⟩ := hall c
      exact ⟨x, (Finset.mem_union.mp hx).resolve_left (fun h => hn ⟨x,h,hxc⟩), hxc⟩

end Se20Insertion.PartialColouring

namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Lemma 11.22, all three conclusions under its operational premise.
The same shell conclusions hold for every other edge at u, without a tree hypothesis. -/
theorem degree_three_rigidity (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) {u v : V} (huv : G.Adj u v)
    (hu : G.degree u = 3) (he : edge G huv ∉ F)
    (hno : ¬ φ.SwapSingleRepair (edge G huv)) :
    let e := edge G huv
    let K := (incident G u).erase e ∪ starBase G u
    let A := (shell G u v).image φ.colour
    (conflicts G e).card = 20 ∧
    (∀ f ∈ conflicts G e, f ∈ F) ∧ Set.InjOn φ.colour (conflicts G e) ∧
    (∀ f ∈ conflicts G e, ∀ c, c ≠ φ.colour f → ∃ x, φ.Neighbour f c x) ∧
    A.card = 9 ∧ K.card = 11 ∧
    ∀ (w : V) (huw : G.Adj u w), w ≠ v →
      (shell G u w).card = 9 ∧ (shell G u w).image φ.colour = A ∧
      (∀ x ∈ shell G u w, x ∈ F) ∧ Set.InjOn φ.colour (shell G u w) ∧
      (∀ c ∈ A, ∃! x, x ∈ shell G u w ∧ φ.colour x = c) ∧
      ∀ (z : V) (huz : G.Adj u z), z ≠ v → z ≠ w →
        ∀ c ∈ A, ∀ x ∈ shell G u z, φ.colour x = c →
          φ.SameComponent (φ.colour (edge G huw)) c (edge G huw) x := by
  let e := edge G huv
  let K := (incident G u).erase e ∪ starBase G u
  change e ∉ F at he
  have hb : ∀ c, ∃ x, φ.Neighbour e c x := by
    intro c; by_contra hc; exact hno (φ.repair_of_free he hc)
  have hbound : (conflicts G e).card ≤ 20 := by
    have hr := card_rim_le_degrees G huv
    have hn := card_conflicts_le_mul_rim G hΔ e (by rfl)
    have hv := hΔ v; omega
  obtain ⟨hn, hF, hinj⟩ := φ.saturated_twenty (conflicts G e) e (mem_conflicts G e) hbound hb
  have hsingle (f : G.edgeSet) (hf : f ∈ conflicts G e) : φ.Single e (φ.colour f) f :=
    ⟨⟨hF f hf, (mem_conflicts G e f).mp hf, rfl⟩,
      fun x hx => hinj ((mem_conflicts G e x).mpr hx.2.1) hf hx.2.2⟩
  have hnt : ∀ a b, a ≠ b → ¬ φ.TriviallySeparable e a b := by
    intro a b hab ht
    obtain ⟨f,hf⟩ := hb a
    have hs : φ.Single e a f := hf.2.2 ▸ hsingle f ((mem_conflicts G e f).mpr hf.2.1)
    exact hno ⟨φ, Or.inl rfl, φ.single_free_insertion he hs hab.symm (ht f hf)⟩
  have hsat := (degree_three_saturated G hΔ φ e (by rfl) hu.le hb hnt).2.2.2
  have hK : K.card ≤ 11 := by
    have hi := Finset.card_erase_add_one (show e ∈ incident G u by simp [e,edge])
    rw [card_incident,hu] at hi
    have hb := starBase_card_le G hΔ u
    have hk := Finset.card_union_le ((incident G u).erase e) (starBase G u)
    dsimp [K]; omega
  have hcover (w : V) (huw : G.Adj u w) :
      ∀ c : Colour, ∃ x ∈ K ∪ shell G u w, x ∈ F ∧ φ.colour x = c := by
    by_cases hwv : w = v
    · subst w
      intro c; obtain ⟨x,hx⟩ := hb c
      refine ⟨x, ?_, hx.1, hx.2.2⟩
      rw [← conflicts_star_decomposition G e (by rfl)]
      exact (mem_conflicts G e x).mpr hx.2.1
    · let f := edge G huw
      have hfe : f ≠ e := by
        intro h
        have h' := congrArg Subtype.val h
        have hh : w = v ∨ u = v ∧ w = u := by simpa [f,e,edge] using h'
        have : w = v := hh.elim id (fun h => h.2.trans h.1)
        exact hwv this
      have hf : f ∈ conflicts G e := (mem_conflicts G e f).mpr
        ⟨hfe.symm, u, by simp [e,edge], u, by simp [f,edge], Or.inl rfl⟩
      intro c
      by_cases hc : c = φ.colour f
      · exact ⟨f, Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hfe, by simp [f,edge]⟩)), hF f hf, hc.symm⟩
      · obtain ⟨x,hx⟩ := hsat f hf c hc
        have hm := (mem_conflicts G f x).mpr hx.2.1
        rw [conflicts_star_decomposition G f (by rfl)] at hm
        refine ⟨x, ?_, hx.1, hx.2.2⟩
        rcases Finset.mem_union.mp hm with hm | hm
        · rcases Finset.mem_union.mp hm with hm | hm
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨fun h => he (h ▸ hx.1), (Finset.mem_erase.mp hm).2⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
        · exact Finset.mem_union_right _ hm
  have split (w : V) (huw : G.Adj u w) :=
    φ.palette_split K (shell G u w) hK (shell_card_le G hΔ huw) (hcover w huw)
  have sp := split v huv
  have hA : ((shell G u v).image φ.colour).card = 9 := by
    rw [Finset.card_image_of_injOn (sp.2.2.2.2.1.mono (by intro x hx; exact Finset.mem_union_right _ hx))]
    exact sp.2.1
  refine ⟨hn, hF, hinj, hsat, hA, sp.1, ?_⟩
  intro w huw hwv
  have sw := split w huw
  have hwi : Set.InjOn φ.colour (shell G u w) := sw.2.2.2.2.1.mono
    (by intro x hx; exact Finset.mem_union_right _ hx)
  have heq : (shell G u w).image φ.colour = (shell G u v).image φ.colour :=
    sw.2.2.2.2.2.trans sp.2.2.2.2.2.symm
  refine ⟨sw.2.1, heq, (fun x hx => sw.2.2.2.1 x (Finset.mem_union_right _ hx)), hwi, ?_, ?_⟩
  · intro c hc
    rw [← heq] at hc
    obtain ⟨x,hx,hxc⟩ := Finset.mem_image.mp hc
    exact ⟨x, ⟨hx,hxc⟩, fun y hy => hwi hy.1 hx (hy.2.trans hxc.symm)⟩
  · intro z huz hzv hzw c hc x hx hxc
    let f := edge G huw
    let g := edge G huz
    have distinct {a b : V} (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) :
        edge G ha ≠ edge G hb := by
      intro h; apply hab
      have hh : a = b ∨ u = b ∧ a = u := by simpa [edge] using congrArg Subtype.val h
      exact hh.elim id (fun h => h.2.trans h.1)
    have hfne := distinct huw huv hwv
    have hgne := distinct huz huv hzv
    have hgfn := distinct huz huw hzw
    have hf : f ∈ K := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfne, by simp [f,edge]⟩)
    have hg : g ∈ K := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hgne, by simp [g,edge]⟩)
    have hfc : φ.colour f ≠ c := by
      rw [sp.2.2.2.2.2] at hc
      exact fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_image.mpr ⟨f,hf,h⟩)
    have hgc : φ.colour g ≠ c := by
      rw [sp.2.2.2.2.2] at hc
      exact fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_image.mpr ⟨g,hg,h⟩)
    have sz := split z huz
    have hgf : (L2 G).Adj g f := ⟨hgfn, u, by simp [g,edge], u, by simp [f,edge], Or.inl rfl⟩
    have hfF := sw.2.2.2.1 f (Finset.mem_union_left _ hf)
    have hgF := sz.2.2.2.1 g (Finset.mem_union_left _ hg)
    have hfgc : φ.colour f ≠ φ.colour g := φ.proper hfF hgF hgf.symm
    have hcolsub {y : G.edgeSet} (hy : y ∈ F) (hgy : (L2 G).Adj g y) :
        y ∈ K ∪ shell G u z := by
      have hm := (mem_conflicts G g y).mpr hgy
      rw [conflicts_star_decomposition G g (by rfl)] at hm
      rcases Finset.mem_union.mp hm with hm | hm
      · rcases Finset.mem_union.mp hm with hm | hm
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨fun h => he (h ▸ hy), (Finset.mem_erase.mp hm).2⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ hm
    have hsg : φ.Single e (φ.colour g) g := hsingle g ((mem_conflicts G e g).mpr
      ⟨hgne.symm,u,by simp [e,edge],u,by simp [g,edge],Or.inl rfl⟩)
    have hsf : φ.Single g (φ.colour f) f := ⟨⟨hfF,hgf,rfl⟩, fun y hy =>
      sz.2.2.2.2.1 (hcolsub hy.1 hy.2.1) (Finset.mem_union_left _ hf) hy.2.2⟩
    by_contra hconn
    have havoid : ∀ y, φ.Neighbour g c y → ¬ φ.SameComponent (φ.colour f) c f y := by
      intro y hy
      have hyx := sz.2.2.2.2.1 (hcolsub hy.1 hy.2.1) (Finset.mem_union_right _ hx) (hy.2.2.trans hxc.symm)
      simpa [hyx] using hconn
    have hr := φ.swap_then_single_insertion he hsg hsf hfc.symm hgc.symm hfgc havoid
    dsimp only at hr
    exact hno ⟨φ.swap (φ.colour f) c {y | φ.SameComponent (φ.colour f) c f y}
      (φ.component_closed (φ.colour f) c f),
      Or.inr ⟨φ.colour f,c,hfc,f,⟨hfF,Or.inl rfl⟩,fun _ => rfl⟩, by
        obtain ⟨θ,hθ⟩ := hr
        refine ⟨{ colour := θ.colour, proper := ?_ }, hθ⟩
        intro q r hq hr hqr
        exact θ.proper (by simpa only [Finset.mem_insert] using hq)
          (by simpa only [Finset.mem_insert] using hr) hqr⟩

end Se20Insertion
