import Se20Part.MultipartiteFive
import Se20Part.PetersenMinusHypothesis
import Se20Part.Critical

noncomputable section
open scoped Classical
namespace Se20Part

/-- A list-colourable induced block extends a fixed outside colouring.
The degree budget counts neighbours in the unchanged ambient graph. -/
theorem list_block_extension {W : Type*} [Fintype W] (H : SimpleGraph W)
    (A B : Finset W) (hdis : Disjoint A B) (k : B → ℕ)
    (hbudget : ∀ v : B, H.degree v.val + k v ≤
      20 + (H.induce (B : Set W)).degree v)
    (hlist : ∀ L : B → Finset Colour, (∀ v, k v ≤ (L v).card) →
      HasListColouring (H.induce (B : Set W)) L)
    (φ : PartialColouring H A) :
    ∃ θ : PartialColouring H (A ∪ B), ∀ a ∈ A, θ.colour a = φ.colour a := by
  let N : B → Finset W := fun v => A.filter (H.Adj v.val)
  let D : B → Finset Colour := fun v => (N v).image φ.colour
  let L : B → Finset Colour := fun v => Finset.univ \ D v
  have hsize : ∀ v, k v ≤ (L v).card := by
    intro v
    have hd := Finset.card_image_le (s := N v) (f := φ.colour)
    have hds : Disjoint (N v) (B.filter (H.Adj v.val)) :=
      hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsub : N v ∪ B.filter (H.Adj v.val) ⊆ H.neighborFinset v.val := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;>
        simpa using (Finset.mem_filter.mp hx).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hds, SimpleGraph.card_neighborFinset_eq_degree,
      ← degree_induce_finset H B v] at hc
    have hl : (L v).card = 20 - (D v).card := by
      simp only [L, Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin]
    have hb := hbudget v
    change (D v).card ≤ (N v).card at hd
    omega
  obtain ⟨c, hc, hp⟩ := hlist L hsize
  let f : W → Colour := fun v => if hv : v ∈ B then c ⟨v,hv⟩ else φ.colour v
  have hfree (v : B) (a : W) (ha : a ∈ A) (hva : H.Adj v.val a) :
      c v ≠ φ.colour a := by
    intro he
    apply (Finset.mem_sdiff.mp (hc v)).2
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hva⟩,he.symm⟩
  refine ⟨⟨f,?_⟩,?_⟩
  · intro u v hu hv huv
    dsimp [f]
    split_ifs with huB hvB hvB
    · exact hp ⟨u,huB⟩ ⟨v,hvB⟩ huv
    · exact hfree ⟨u,huB⟩ v ((Finset.mem_union.mp hv).resolve_right hvB) huv
    · exact (hfree ⟨v,hvB⟩ u ((Finset.mem_union.mp hu).resolve_right huB) huv.symm).symm
    · exact φ.proper ((Finset.mem_union.mp hu).resolve_right huB)
        ((Finset.mem_union.mp hv).resolve_right hvB) huv
  · intro a ha
    exact dif_neg (fun hb => Finset.disjoint_left.mp hdis ha hb)

theorem list_block_extension_of_iso {W U : Type*} [Fintype W] [Fintype U]
    (H : SimpleGraph W) (Q : SimpleGraph U) (A B : Finset W) (hdis : Disjoint A B)
    (f : Q ≃g H.induce (B : Set W)) (k : U → ℕ)
    (hbudget : ∀ u, H.degree (f u).val + k u ≤ 20 + Q.degree u)
    (hlist : ∀ L : U → Finset Colour, (∀ u, k u ≤ (L u).card) → HasListColouring Q L)
    (φ : PartialColouring H A) :
    ∃ θ : PartialColouring H (A ∪ B), ∀ a ∈ A, θ.colour a = φ.colour a := by
  apply list_block_extension H A B hdis (fun v => k (f.symm v)) _ _ φ
  · intro v
    have hb := hbudget (f.symm v)
    rw [f.symm.degree_eq] at hb
    simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hb ⊢
    simpa only [RelIso.apply_symm_apply] using hb
  · intro L hL
    obtain ⟨c,hc,hp⟩ := hlist (fun u => L (f u)) (fun u => by simpa using hL (f u))
    refine ⟨fun v => c (f.symm v),?_,?_⟩
    · intro v; simpa using hc (f.symm v)
    · intro u v huv; exact hp _ _ (f.symm.toHom.map_adj huv)

theorem threePart_five_degree (v : Fin 5 × Fin 3) :
    (ThreePartGraph (Fin 5)).degree v = 12 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
  letI : DecidableRel (ThreePartGraph (Fin 5)).Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))
  rw [← Fintype.card_eq_nat_card, SimpleGraph.card_neighborSet_eq_degree]
  have h : ∀ v, (ThreePartGraph (Fin 5)).degree v = 12 := by decide +kernel
  exact h v

/-- The complete G14 eight-list interface, preserving every outside colour. -/
theorem threePart_five_block_extension {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hΔ : ∀ w, H.degree w ≤ 24) (A B : Finset W) (hdis : Disjoint A B)
    (f : ThreePartGraph (Fin 5) ≃g H.induce (B : Set W)) (φ : PartialColouring H A) :
    ∃ θ : PartialColouring H (A ∪ B), ∀ a ∈ A, θ.colour a = φ.colour a := by
  apply list_block_extension_of_iso H _ A B hdis f (fun _ => 8) _ _ φ
  · intro u; rw [threePart_five_degree]; have := hΔ (f u).val; omega
  · intro L hL; exact five_parts_eight_choosable (by simp) L hL

/-- The G15 hypothesis is used only as an explicit arbitrary-list argument. -/
theorem petersenMinus_block_extension {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hG15 : PetersenMinusListTheoremG15) (hΔ : ∀ w, H.degree w ≤ 24)
    (A B : Finset W) (hdis : Disjoint A B)
    (f : PetersenMinusConflict ≃g H.induce (B : Set W)) (φ : PartialColouring H A) :
    ∃ θ : PartialColouring H (A ∪ B), ∀ a ∈ A, θ.colour a = φ.colour a := by
  apply list_block_extension_of_iso H _ A B hdis f petersenMinusListSize _ _ φ
  · intro u; rw [petersenMinus_degrees]; have := hΔ (f u).val; omega
  · exact hG15 Colour

end Se20Part
