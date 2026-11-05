import Se20Insertion.ParametricCore

noncomputable section
open scoped Classical
namespace Se20Insertion.Parametric.PartialColouring
variable {K : Nat} {W : Type*} {H : SimpleGraph W} {F : Finset W}

def outsideYNeighbours (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) (v : W) : Finset W :=
  domainNeighbours H (insert h F) v \ φ.yNeighbours Y v

theorem yNeighbours_subset_domain (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) (v : W) :
    φ.yNeighbours Y v ⊆ domainNeighbours H (insert h F) v := by
  intro x hx
  obtain ⟨hxF, hvx, _⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hxF, hvx⟩

theorem outsideYNeighbours_card (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) (v : W) :
    (φ.outsideYNeighbours h Y v).card + (φ.yNeighbours Y v).card =
      (domainNeighbours H (insert h F) v).card := by
  exact Finset.card_sdiff_add_card_eq_card (φ.yNeighbours_subset_domain h Y v)

theorem threshold_eq_outside (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K)) (v : W) :
    φ.colourSetThreshold h Y v =
      2 * ((K : Int) - (Y.card : Int)) - (φ.outsideYNeighbours h Y v).card := by
  have := φ.outsideYNeighbours_card h Y v
  unfold colourSetThreshold
  omega

theorem core_neighbours_subset_outside (φ : PartialColouring K H F) (h : W)
    (Y : Finset (Fin K)) (v : W) :
    domainNeighbours H (φ.colourSetCore h Y) v ⊆ φ.outsideYNeighbours h Y v := by
  intro x hx
  obtain ⟨hxC, hvx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxD, hxY, _⟩ := Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hxC)
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hxD, hvx⟩, ?_⟩
  intro hx
  obtain ⟨hxF, _, hc⟩ := Finset.mem_filter.mp hx
  exact hxY hxF hc

theorem core_degree_bound (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K))
    {v : W} (hv : v ∈ φ.colourSetCore h Y) :
    2 * ((φ.yNeighbours Y v).card : ℤ) ≤
      2 * (domainNeighbours H (insert h F) v).card - 2 * ((K : Int) - (Y.card : Int)) := by
  have hlow := (φ.colourSetCore_isCore h Y).2 v hv
  have hupp := Finset.card_le_card (φ.core_neighbours_subset_outside h Y v)
  have hparts := φ.outsideYNeighbours_card h Y v
  unfold colourSetThreshold at hlow
  omega

theorem allTangled_sees (φ : PartialColouring K H F) {Y : Finset (Fin K)} {v : W}
    (hY : 2 ≤ Y.card) (ht : φ.AllTangled Y v) : ∀ a ∈ Y, ∃ x, φ.Neighbour v a x := by
  intro a ha
  have hex : ∃ b ∈ Y, b ≠ a := by
    by_contra hn
    push_neg at hn
    have hsub : Y ⊆ {a} := by intro b hb; simpa using hn b hb
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨b, hb, hba⟩ := hex
  obtain ⟨x, y, hx, _, _⟩ := ht a ha b hb hba.symm
  exact ⟨x, hx⟩

theorem core_yDegree_lower (φ : PartialColouring K H F) (h : W) (Y : Finset (Fin K))
    (hY : 2 ≤ Y.card) {v : W} (hv : v ∈ φ.colourSetCore h Y) :
    Y.card ≤ (φ.yNeighbours Y v).card := by
  have ht := (Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hv)).2.2
  have hsub : Y ⊆ (φ.yNeighbours Y v).image φ.colour := by
    intro a ha
    obtain ⟨x, hxF, hvx, hxa⟩ := φ.allTangled_sees hY ht a ha
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxF, hvx, hxa ▸ ha⟩, hxa⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le


def colourGroups (k : ℕ) : Finset (Finset (Fin K)) := Finset.univ.powersetCard k

theorem mem_colourGroups {k : ℕ} {Y : Finset (Fin K)} : Y ∈ colourGroups (K := K) k ↔ Y.card = k := by
  simp [colourGroups]

theorem card_colourGroups (k : ℕ) : (colourGroups (K := K) k).card = Nat.choose K k := by
  simp [colourGroups]

theorem card_groups_avoiding (k : ℕ) (a : (Fin K)) :
    ((colourGroups (K := K) k).filter (fun Y => a ∉ Y)).card = Nat.choose (K - 1) k := by
  have heq : (colourGroups (K := K) k).filter (fun Y => a ∉ Y) =
      (Finset.univ.erase a).powersetCard k := by
    ext Y
    simp only [Finset.mem_filter, mem_colourGroups, Finset.mem_powersetCard]
    have hsub : Y ⊆ (Finset.univ : Finset (Fin K)).erase a ↔ a ∉ Y := by
      simp [Finset.subset_iff, Finset.mem_erase]
    rw [hsub]
    tauto
  rw [heq, Finset.card_powersetCard]
  simp

/-- Unordered k-cliques of the tangling graph, excluding the vertex's own colour. -/
def tangleCliqueCount (φ : PartialColouring K H F) (k : ℕ) (f : W) : ℕ :=
  ((colourGroups (K := K) k).filter (fun Y => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card

/-- Double counting incidence pairs, expressed using filters. -/
theorem sum_filter_card_swap {A B : Type*} (s : Finset A) (t : Finset B) (r : A → B → Prop)
    [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, (t.filter (r a)).card) = ∑ b ∈ t, (s.filter (fun a => r a b)).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_groups_avoiding (φ : PartialColouring K H F) (N : Finset W) (k : ℕ) :
    (∑ Y ∈ colourGroups (K := K) k, (N.filter (fun f => φ.colour f ∉ Y)).card) =
      N.card * Nat.choose (K - 1) k := by
  rw [sum_filter_card_swap (colourGroups (K := K) k) N (fun Y f => φ.colour f ∉ Y)]
  simp [card_groups_avoiding]

def AllGroupsFail (φ : PartialColouring K H F) (h : W) (k : ℕ) : Prop :=
  ∀ Y ∈ colourGroups (K := K) k, h ∈ φ.colourSetCore h Y

theorem allGroupsFail_tangled (φ : PartialColouring K H F) {h : W} {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ K) (hf : φ.AllGroupsFail h k) :
    ∀ a b, a ≠ b → φ.TangledAt h a b := by
  intro a b hab
  obtain ⟨Y, hpair, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ ({a, b} : Finset (Fin K))) (by simpa [hab] using hk)
    (show k ≤ (Finset.univ : Finset (Fin K)).card by simpa using hk')
  have hh := hf Y (mem_colourGroups.mpr hcard)
  have ht := (Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hh)).2.2
  exact ht a (hpair (by simp)) b (hpair (by simp)) hab

theorem hole_domainNeighbours (φ : PartialColouring K H F) (h : W) :
    domainNeighbours H (insert h F) h = φ.colouredNeighbours h := by
  ext x
  simp only [domainNeighbours, colouredNeighbours, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hx, hhx⟩
    exact ⟨hx.resolve_left hhx.ne.symm, hhx⟩
  · rintro ⟨hx, hhx⟩
    exact ⟨Or.inr hx, hhx⟩


end Se20Insertion.Parametric.PartialColouring
