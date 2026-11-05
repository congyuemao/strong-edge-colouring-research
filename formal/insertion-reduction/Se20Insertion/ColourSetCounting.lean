import Se20Insertion.ColourSetSpecialCases

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def colourGroups (k : ℕ) : Finset (Finset Colour) := Finset.univ.powersetCard k

theorem mem_colourGroups {k : ℕ} {Y : Finset Colour} : Y ∈ colourGroups k ↔ Y.card = k := by
  simp [colourGroups]

theorem card_colourGroups (k : ℕ) : (colourGroups k).card = Nat.choose 20 k := by
  simp [colourGroups]

theorem card_groups_avoiding (k : ℕ) (a : Colour) :
    ((colourGroups k).filter (fun Y => a ∉ Y)).card = Nat.choose 19 k := by
  have heq : (colourGroups k).filter (fun Y => a ∉ Y) =
      (Finset.univ.erase a).powersetCard k := by
    ext Y
    simp only [Finset.mem_filter, mem_colourGroups, Finset.mem_powersetCard]
    have hsub : Y ⊆ (Finset.univ : Finset Colour).erase a ↔ a ∉ Y := by
      simp [Finset.subset_iff, Finset.mem_erase]
    rw [hsub]
    tauto
  rw [heq, Finset.card_powersetCard]
  simp

/-- Unordered k-cliques of the tangling graph, excluding the vertex's own colour. -/
def tangleCliqueCount (φ : PartialColouring H F) (k : ℕ) (f : W) : ℕ :=
  ((colourGroups k).filter (fun Y => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card

/-- Double counting incidence pairs, expressed using filters. -/
theorem sum_filter_card_swap {A B : Type*} (s : Finset A) (t : Finset B) (r : A → B → Prop)
    [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, (t.filter (r a)).card) = ∑ b ∈ t, (s.filter (fun a => r a b)).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_groups_avoiding (φ : PartialColouring H F) (N : Finset W) (k : ℕ) :
    (∑ Y ∈ colourGroups k, (N.filter (fun f => φ.colour f ∉ Y)).card) =
      N.card * Nat.choose 19 k := by
  rw [sum_filter_card_swap (colourGroups k) N (fun Y f => φ.colour f ∉ Y)]
  simp [card_groups_avoiding]

def AllGroupsFail (φ : PartialColouring H F) (h : W) (k : ℕ) : Prop :=
  ∀ Y ∈ colourGroups k, h ∈ φ.colourSetCore h Y

theorem allGroupsFail_tangled (φ : PartialColouring H F) {h : W} {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 20) (hf : φ.AllGroupsFail h k) :
    ∀ a b, a ≠ b → φ.TangledAt h a b := by
  intro a b hab
  obtain ⟨Y, hpair, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ ({a, b} : Finset Colour)) (by simpa [hab] using hk)
    (show k ≤ (Finset.univ : Finset Colour).card by simpa using hk')
  have hh := hf Y (mem_colourGroups.mpr hcard)
  have ht := (Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hh)).2.2
  exact ht a (hpair (by simp)) b (hpair (by simp)) hab

theorem allGroupsFail_stuck (φ : PartialColouring H F) {h : W} {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 20) (hf : φ.AllGroupsFail h k) : φ.Stuck h := by
  have ht := φ.allGroupsFail_tangled hk hk' hf
  refine ⟨?_, fun a b hab => (φ.tangledAt_iff_not_separable h a b).mp (ht a b hab)⟩
  intro a
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨x, y, hx, _, _⟩ := ht a b hb.symm
  exact ⟨x, hx⟩

theorem allGroupsFail_single_saturated (φ : PartialColouring H F) {h f : W} {k : ℕ}
    {u : Colour} (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hs : φ.Single h u f) : ∀ a, a ≠ u → ∃ x, φ.Neighbour f a x :=
  φ.single_saturated_of_stuck hs (φ.allGroupsFail_stuck hk (by omega) hf)

theorem hole_domainNeighbours (φ : PartialColouring H F) (h : W) :
    domainNeighbours H (insert h F) h = φ.colouredNeighbours h := by
  ext x
  simp only [domainNeighbours, colouredNeighbours, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hx, hhx⟩
    exact ⟨hx.resolve_left hhx.ne.symm, hhx⟩
  · rintro ⟨hx, hhx⟩
    exact ⟨Or.inr hx, hhx⟩

theorem allGroupsFail_at_least_sixteen_single (φ : PartialColouring H F) {h : W} {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hd : (domainNeighbours H (insert h F) h).card = 24) :
    16 ≤ (φ.singleColours h).card := by
  have hb := φ.blocked_single_count h (φ.allGroupsFail_stuck hk (by omega) hf).1
  rw [φ.hole_domainNeighbours] at hd
  omega

/-- Proposition 11.49(2), proved by summing the outside-colour incidences. -/
theorem allGroupsFail_clique_sum (φ : PartialColouring H F) (h : W) {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hd : (domainNeighbours H (insert h F) h).card = 24) :
    3 * (∑ f ∈ domainNeighbours H (insert h F) h, φ.tangleCliqueCount k f) ≥
      2 * 24 * Nat.choose 19 k := by
  let N := domainNeighbours H (insert h F) h
  have hNF : N ⊆ F := by
    change domainNeighbours H (insert h F) h ⊆ F
    rw [φ.hole_domainNeighbours]
    exact Finset.filter_subset _ _
  have hlocal : ∀ Y ∈ colourGroups k,
      2 * (20 - k) ≤ (N.filter (fun f => φ.colour f ∉ Y)).card +
        (N.filter (fun f => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card := by
    intro Y hY
    have hcard := mem_colourGroups.mp hY
    have hcore := (φ.colourSetCore_isCore h Y).2 h (hf Y hY)
    have ho : φ.outsideYNeighbours h Y h = N.filter (fun f => φ.colour f ∉ Y) := by
      ext f
      simp only [outsideYNeighbours, Finset.mem_sdiff, Finset.mem_filter, yNeighbours]
      constructor
      · rintro ⟨hfN, hn⟩
        exact ⟨hfN, fun hc => hn ⟨hNF hfN, (Finset.mem_filter.mp hfN).2, hc⟩⟩
      · rintro ⟨hfN, hc⟩
        exact ⟨hfN, fun hm => hc hm.2.2⟩
    have hsub : domainNeighbours H (φ.colourSetCore h Y) h ⊆
        N.filter (fun f => φ.colour f ∉ Y ∧ φ.AllTangled Y f) := by
      intro f hf'
      obtain ⟨hfC, hhf⟩ := Finset.mem_filter.mp hf'
      obtain ⟨hfD, hfY, ht⟩ := Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hfC)
      have hfN : f ∈ N := Finset.mem_filter.mpr ⟨hfD, hhf⟩
      exact Finset.mem_filter.mpr ⟨hfN, hfY (hNF hfN), ht⟩
    have hle := Finset.card_le_card hsub
    rw [φ.threshold_eq_outside, ho, hcard] at hcore
    omega
  have hsum := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, φ.sum_groups_avoiding] at hsum
  have hswap := sum_filter_card_swap (colourGroups k) N
    (fun Y f => φ.colour f ∉ Y ∧ φ.AllTangled Y f)
  change (∑ Y ∈ colourGroups k, (N.filter (fun f => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card) =
    ∑ f ∈ N, φ.tangleCliqueCount k f at hswap
  rw [hswap] at hsum
  have hchoose : Nat.choose 20 k * (20 - k) = Nat.choose 19 k * 20 :=
    (Nat.choose_mul_succ_eq 19 k).symm
  have hN : N.card = 24 := hd
  simp only [Finset.sum_const, smul_eq_mul, card_colourGroups, hN] at hsum
  nlinarith

/-- Each two-element set is counted once; the vertex's own colour is excluded. -/
def separablePairCount (φ : PartialColouring H F) (f : W) : ℕ :=
  ((colourGroups 2).filter (fun Y => φ.colour f ∉ Y ∧ ¬ φ.AllTangled Y f)).card

theorem not_allTangled_iff_separable (φ : PartialColouring H F) (Y : Finset Colour) (f : W) :
    ¬ φ.AllTangled Y f ↔ ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧ φ.Separable f a b := by
  simp only [AllTangled, tangledAt_iff_not_separable]
  push_neg
  rfl

theorem clique_pair_partition (φ : PartialColouring H F) (f : W) :
    φ.tangleCliqueCount 2 f + φ.separablePairCount f = 171 := by
  have hc := Finset.card_filter_add_card_filter_not
    (s := (colourGroups 2).filter (fun Y => φ.colour f ∉ Y)) (p := fun Y => φ.AllTangled Y f)
  simpa only [Finset.filter_filter, card_groups_avoiding, tangleCliqueCount,
    separablePairCount, show Nat.choose 19 2 = 171 from by decide] using hc

/-- The one-layer inequality in 11.51 implies that some two-colour core succeeds. -/
theorem good_pair_of_separable_sum (φ : PartialColouring H F) (h : W)
    (hd : (domainNeighbours H (insert h F) h).card = 24)
    (hsep : 1368 < ∑ f ∈ domainNeighbours H (insert h F) h, φ.separablePairCount f) :
    ∃ Y ∈ colourGroups 2, h ∉ φ.colourSetCore h Y := by
  by_contra hn
  have hf : φ.AllGroupsFail h 2 := by
    intro Y hY
    by_contra hnot
    exact hn ⟨Y, hY, hnot⟩
  have hlow := φ.allGroupsFail_clique_sum h (by decide) (by decide) hf hd
  have hpart := Finset.sum_congr rfl (fun f (_ : f ∈ domainNeighbours H (insert h F) h) =>
    φ.clique_pair_partition f)
  rw [Finset.sum_add_distrib] at hpart
  simp only [Finset.sum_const, smul_eq_mul, hd] at hpart
  norm_num [Nat.choose] at hlow
  omega

theorem insertion_of_separable_sum (φ : PartialColouring H F) (h : W) (hh : h ∉ F)
    (hd : (domainNeighbours H (insert h F) h).card = 24)
    (hsep : 1368 < ∑ f ∈ domainNeighbours H (insert h F) h, φ.separablePairCount f) :
    Nonempty (PartialColouring H (insert h F)) := by
  obtain ⟨Y, hY, hcore⟩ := φ.good_pair_of_separable_sum h hd hsep
  exact φ.colourSetInsertion h hh Y (by rw [mem_colourGroups.mp hY]) hcore

end PartialColouring
end Se20Insertion
