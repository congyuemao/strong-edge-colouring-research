import Se20Part.CriticalExtraction
import Se20Part.High24Seven
import Se20Part.DiffuseSaturation

noncomputable section
open scoped Classical
namespace Se20Part

/-- The abstract obstruction returned by the finite G05 checks. The check
knows nothing about an original graph, edge sets, or strong colouring. -/
def AbstractTwentyObstruction {W : Type*} [Fintype W] (H : SimpleGraph W) : Prop :=
  (∃ Q : Finset W, Q.card = 20 ∧ H.IsClique (Q : Set W)) ∨
  (∃ Q : Finset W, Q.card = 8 ∧ H.IsClique (Q : Set W) ∧ ∀ v ∈ Q, H.degree v = 24)

/-- Explicit finite-check interface, with labelled simple graphs as inputs.
This definition is NOT an executed check or a theorem. -/
def AbstractCriticalCheck (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → n ≤ hi → ∀ H : SimpleGraph (Fin n),
    (∀ v, H.degree v ≤ 24) → ¬ H.Colorable 20 → AbstractTwentyObstruction H

/-- Unverified finite check: orders 21,...,25, exactly
`∑ n ∈ {21,...,25}, 2^(n*(n-1)/2)` labelled graph inputs. -/
def G05SmallAbstractCheck : Prop := AbstractCriticalCheck 21 25

/-- Unverified finite check: orders 26,...,40, exactly
`∑ n ∈ {26,...,40}, 2^(n*(n-1)/2)` labelled graph inputs. -/
def G05MiddleAbstractCheck : Prop := AbstractCriticalCheck 26 40

/-- Unverified finite check: order 41, exactly `2^820` labelled graph
inputs, before the maximum-degree and non-colourability filters. -/
def G05BoundaryAbstractCheck : Prop := AbstractCriticalCheck 41 41

theorem embedding_degree_le {W X : Type*} [Fintype W] [Fintype X]
    {H : SimpleGraph W} {J : SimpleGraph X} (f : H ↪g J) (v : W) :
    H.degree v ≤ J.degree (f v) := by
  let q : H.neighborSet v → J.neighborSet (f v) := fun x => ⟨f x,f.toHom.map_adj x.prop⟩
  have hq : Function.Injective q := by
    intro x y h
    exact Subtype.ext (f.injective (congrArg Subtype.val h))
  have hc := Fintype.card_le_of_injective q hq
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hc

theorem abstractCriticalCheck_transfer {lo hi : ℕ} (hcheck : AbstractCriticalCheck lo hi)
    {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hlo : lo ≤ Fintype.card W) (hhi : Fintype.card W ≤ hi)
    (hΔ : ∀ v, H.degree v ≤ 24) (hn : ¬ H.Colorable 20) : AbstractTwentyObstruction H := by
  let e := (Fintype.equivFin W).symm
  let J := H.comap e
  let f : J ≃g H := SimpleGraph.Iso.comap e H
  have hd : ∀ v, J.degree v ≤ 24 := fun v => (f.degree_eq v).symm.trans_le (hΔ (f v))
  have hnc : ¬ J.Colorable 20 := fun hc => hn ⟨hc.some.comap f.symm.toHom⟩
  have hobs := hcheck (Fintype.card W) hlo hhi J hd hnc
  rcases hobs with ⟨Q,hq,hcl⟩|⟨Q,hq,hcl,hdeg⟩
  · refine Or.inl ⟨Q.image f,?_,?_⟩
    · rwa [Finset.card_image_of_injective _ f.injective]
    · intro a ha b hb hab
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
      exact f.toHom.map_adj (hcl hx hy (fun h => hab (congrArg f h)))
  · refine Or.inr ⟨Q.image f,?_,?_,?_⟩
    · rwa [Finset.card_image_of_injective _ f.injective]
    · intro a ha b hb hab
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
      exact f.toHom.map_adj (hcl hx hy (fun h => hab (congrArg f h)))
    · intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      exact (f.degree_eq x).trans (hdeg x hx)

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The geometric part of G05 is unconditional: neither abstract obstruction
can occur in a 21-critical ambient edge set. -/
theorem critical21_no_abstract_obstruction (hΔ : MaxDegreeFour G)
    {F : Finset G.edgeSet} (hF : Critical21 G F) :
    ¬ AbstractTwentyObstruction ((L2 G).induce (F : Set G.edgeSet)) := by
  let H := (L2 G).induce (F : Set G.edgeSet)
  let f : H ↪g L2 G := SimpleGraph.Embedding.induce (F : Set G.edgeSet)
  have image_clique (Q : Finset F) (hQ : H.IsClique (Q : Set F)) :
      (L2 G).IsClique (Q.image Subtype.val : Set G.edgeSet) := by
    intro a ha b hb hab
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    exact hQ hx hy (fun h => hab (congrArg Subtype.val h))
  rintro (⟨Q,hq,hcl⟩|⟨Q,hq,hcl,hdeg⟩)
  · have hbound := critical21_clique_nineteen G hΔ hF (Q.image Subtype.val)
      (by intro a ha; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ha; exact x.prop) (image_clique Q hcl)
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hq] at hbound
    omega
  · have hbound := high24_clique_seven G hΔ (Q.image Subtype.val) (image_clique Q hcl) (by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      have hl := embedding_degree_le f x
      have hu := conflict_degree_le_twentyFour G hΔ x
      have he := hdeg x hx
      change H.degree x = 24 at he
      change H.degree x ≤ (L2 G).degree x.val at hl
      omega)
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hq] at hbound
    omega

/-- G05's 42-edge conclusion, explicitly conditional on three unexecuted
finite abstract-graph checks. No instance of those checks is asserted. -/
theorem critical21_fortyTwo_of_finite_checks
    (hSmall : G05SmallAbstractCheck) (hMiddle : G05MiddleAbstractCheck)
    (hBoundary : G05BoundaryAbstractCheck) (hΔ : MaxDegreeFour G)
    {F : Finset G.edgeSet} (hF : Critical21 G F) : 42 ≤ F.card := by
  by_contra hn
  have hlo : 21 ≤ F.card := by
    by_contra hn
    exact hF.2.1 (colourable_of_finset_card (L2 G) F 20 (by omega))
  let H := (L2 G).induce (F : Set G.edgeSet)
  have hd : ∀ v : F, H.degree v ≤ 24 := fun v =>
    (embedding_degree_le (SimpleGraph.Embedding.induce (F : Set G.edgeSet)) v).trans
      (conflict_degree_le_twentyFour G hΔ v)
  apply critical21_no_abstract_obstruction G hΔ hF
  by_cases h25 : F.card ≤ 25
  · exact abstractCriticalCheck_transfer hSmall H (by simpa using hlo) (by simpa using h25) hd hF.2.1
  by_cases h40 : F.card ≤ 40
  · exact abstractCriticalCheck_transfer hMiddle H (by simpa using (show 26 ≤ F.card by omega))
      (by simpa using h40) hd hF.2.1
  exact abstractCriticalCheck_transfer hBoundary H (by simpa using (show 41 ≤ F.card by omega))
    (by simpa using (show F.card ≤ 41 by omega)) hd hF.2.1

theorem small_edge_set_twenty_of_finite_checks
    (hSmall : G05SmallAbstractCheck) (hMiddle : G05MiddleAbstractCheck)
    (hBoundary : G05BoundaryAbstractCheck) (hΔ : MaxDegreeFour G)
    (F : Finset G.edgeSet) (hsize : F.card ≤ 41) :
    ((L2 G).induce (F : Set G.edgeSet)).Colorable 20 := by
  by_contra hn
  obtain ⟨A,hAF,hA⟩ := exists_critical21 G hn
  have hl := critical21_fortyTwo_of_finite_checks G hSmall hMiddle hBoundary hΔ hA
  have hu := Finset.card_le_card hAF
  omega

/-- The requested independence-number-two assertion follows using only the
first two finite checks: the already proved packing bound gives |F|≤40. -/
theorem rank_two_twenty_of_finite_checks
    (hSmall : G05SmallAbstractCheck) (hMiddle : G05MiddleAbstractCheck)
    (hΔ : MaxDegreeFour G) (F : Finset G.edgeSet) (hr : packingRank (L2 G) F ≤ 2) :
    ((L2 G).induce (F : Set G.edgeSet)).Colorable 20 := by
  have hsize := rank_two_card_le_forty G hΔ F hr
  by_contra hn
  obtain ⟨A,hAF,hA⟩ := exists_critical21 G hn
  have hA40 : A.card ≤ 40 := (Finset.card_le_card hAF).trans hsize
  have hA21 : 21 ≤ A.card := by
    by_contra hn
    exact hA.2.1 (colourable_of_finset_card (L2 G) A 20 (by omega))
  let H := (L2 G).induce (A : Set G.edgeSet)
  have hd : ∀ v : A, H.degree v ≤ 24 := fun v =>
    (embedding_degree_le (SimpleGraph.Embedding.induce (A : Set G.edgeSet)) v).trans
      (conflict_degree_le_twentyFour G hΔ v)
  apply critical21_no_abstract_obstruction G hΔ hA
  by_cases h25 : A.card ≤ 25
  · exact abstractCriticalCheck_transfer hSmall H (by simpa using hA21) (by simpa using h25) hd hA.2.1
  · exact abstractCriticalCheck_transfer hMiddle H (by simpa using (show 26 ≤ A.card by omega))
      (by simpa using hA40) hd hA.2.1

end Se20Part
