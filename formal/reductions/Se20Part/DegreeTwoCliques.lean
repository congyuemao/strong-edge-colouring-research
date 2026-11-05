import Se20Part.GirthCliques

noncomputable section
open scoped Classical
open Finset
namespace Se20Part
open Legacy

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Degrees in the selected edge set, with all conflicts still taken in G. -/
def DegreeTwoEdgeSet (Q : Finset G.edgeSet) : Prop :=
  ∀ v, (Q.filter (fun e => v ∈ e.val)).card ≤ 2

namespace GirthClique

theorem degreeTwo_branch_card (Q : Finset G.edgeSet) (hdeg : DegreeTwoEdgeSet G Q) (u a : V) :
    (branchEdges G Q u a).card ≤ 2 := by
  apply (card_le_card (show branchEdges G Q u a ⊆ Q.filter (fun e => a ∈ e.val) from ?_)).trans (hdeg a)
  intro e he
  obtain ⟨he,ha,_⟩ := (mem_branchEdges G Q u a e).mp he
  exact mem_filter.mpr ⟨he,ha⟩

theorem degreeTwo_star_card_one (Q : Finset G.edgeSet) (hdeg : DegreeTwoEdgeSet G Q)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u,v)) :
    (branchEdges G Q u v).card ≤ 1 := by
  have hs : insert e (branchEdges G Q u v) ⊆ Q.filter (fun f => v ∈ f.val) := by
    intro f hf
    rcases mem_insert.mp hf with rfl|hf
    · exact mem_filter.mpr ⟨heQ,he ▸ Sym2.mem_mk_right u v⟩
    · obtain ⟨hf,hv,_⟩ := (mem_branchEdges G Q u v f).mp hf
      exact mem_filter.mpr ⟨hf,hv⟩
  have hn : e ∉ branchEdges G Q u v := by
    intro hh
    exact ((mem_branchEdges G Q u v e).mp hh).2.2 (he ▸ Sym2.mem_mk_left u v)
  have hc := (card_le_card hs).trans (hdeg v)
  rw [card_insert_of_notMem hn] at hc
  omega

theorem girth_degreeTwo_branch_union (hΔ : MaxDegreeFour G) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 5 ≤ G.egirth) (hdeg : DegreeTwoEdgeSet G Q)
    (u : V) (A : Finset V) (hAu : ∀ a ∈ A, G.Adj u a) :
    (A.biUnion (branchEdges G Q u)).card ≤ 2 := by
  by_cases hbig : ∃ a ∈ A, 1 < (branchEdges G Q u a).card
  · obtain ⟨a,ha,hbig⟩ := hbig
    obtain ⟨e₁,h₁,e₂,h₂,hne⟩ := one_lt_card.mp hbig
    have hs : A.biUnion (branchEdges G Q u) ⊆ branchEdges G Q u a := by
      intro f hf
      obtain ⟨b,hb,hfb⟩ := mem_biUnion.mp hf
      by_cases hba : b = a
      · simpa only [hba] using hfb
      · exact (girth_mixed_branches_cannot_have_fork G hΔ Q hQ h24
          (hAu a ha) (hAu b hb) (Ne.symm hba) e₁ e₂ f h₁ h₂ hfb hne).elim
    exact (card_le_card hs).trans (degreeTwo_branch_card G Q hdeg u a)
  have hsmall : ∀ a ∈ A, (branchEdges G Q u a).card ≤ 1 := by
    intro a ha
    by_contra hn
    exact hbig ⟨a,ha,by omega⟩
  by_contra hn
  obtain ⟨T,hTU,hT⟩ := exists_subset_card_eq (by omega : 3 ≤ (A.biUnion (branchEdges G Q u)).card)
  obtain ⟨e,f,g,hef,heg,hfg,hset⟩ := card_eq_three.mp hT
  have heU := hTU (show e ∈ T by rw [hset]; simp)
  have hfU := hTU (show f ∈ T by rw [hset]; simp)
  have hgU := hTU (show g ∈ T by rw [hset]; simp)
  obtain ⟨a,ha,hea⟩ := mem_biUnion.mp heU
  obtain ⟨b,hb,hfb⟩ := mem_biUnion.mp hfU
  obtain ⟨c,hc,hgc⟩ := mem_biUnion.mp hgU
  have hab : a ≠ b := fun h => hef (card_le_one.mp (hsmall a ha) e hea f (h ▸ hfb))
  have hac : a ≠ c := fun h => heg (card_le_one.mp (hsmall a ha) e hea g (h ▸ hgc))
  have hbc : b ≠ c := fun h => hfg (card_le_one.mp (hsmall b hb) f hfb g (h ▸ hgc))
  obtain ⟨heQ,hae,hue⟩ := (mem_branchEdges G Q u a e).mp hea
  obtain ⟨hfQ,hbf,huf⟩ := (mem_branchEdges G Q u b f).mp hfb
  obtain ⟨hgQ,hcg,hug⟩ := (mem_branchEdges G Q u c g).mp hgc
  obtain ⟨x,hex⟩ := Sym2.mem_iff_exists.mp hae
  obtain ⟨y,hfy⟩ := Sym2.mem_iff_exists.mp hbf
  obtain ⟨z,hgz⟩ := Sym2.mem_iff_exists.mp hcg
  have hxu : x ≠ u := fun h => hue (hex ▸ h ▸ Sym2.mem_mk_right a x)
  have hyu : y ≠ u := fun h => huf (hfy ▸ h ▸ Sym2.mem_mk_right b y)
  have hzu : z ≠ u := fun h => hug (hgz ▸ h ▸ Sym2.mem_mk_right c z)
  have hxy := girth_external_conflict_adj G hΔ e f hex hfy (h24 e heQ) (h24 f hfQ)
    (hAu a ha) (hAu b hb) hab hxu hyu (hQ heQ hfQ hef)
  have hxz := girth_external_conflict_adj G hΔ e g hex hgz (h24 e heQ) (h24 g hgQ)
    (hAu a ha) (hAu c hc) hac hxu hzu (hQ heQ hgQ heg)
  have hyz := girth_external_conflict_adj G hΔ f g hfy hgz (h24 f hfQ) (h24 g hgQ)
    (hAu b hb) (hAu c hc) hbc hyu hzu (hQ hfQ hgQ hfg)
  exact GirthFive.no_triangle (h24 e heQ) hxy hyz hxz.symm

theorem girth_degreeTwo_side (hΔ : MaxDegreeFour G) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h24 : ∀ e ∈ Q, 5 ≤ G.egirth) (hdeg : DegreeTwoEdgeSet G Q) (u v : V) :
    (((G.neighborFinset u).erase v).biUnion (branchEdges G Q u)).card ≤ 2 :=
  girth_degreeTwo_branch_union G hΔ Q hQ h24 hdeg u _
    (fun a ha => (G.mem_neighborFinset _ _).mp (mem_erase.mp ha).2)

end GirthClique
end Se20Part
