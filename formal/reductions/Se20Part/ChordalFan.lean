import Se20Part.ForestL2

noncomputable section
open scoped Classical
namespace Se20Part
namespace ChordalFan
variable {W : Type*} {H : SimpleGraph W}

/-- An indexed induced path with `n` steps and `n+1` vertices. -/
structure InducedPath (H : SimpleGraph W) (p : ℕ → W) (n : ℕ) : Prop where
  inj : ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j
  step : ∀ i < n, H.Adj (p i) (p (i+1))
  no_chord : ∀ i j, i+1 < j → j ≤ n → ¬ H.Adj (p i) (p j)

def Eliminates (H : SimpleGraph W) (r : W → ℕ) : Prop :=
  ∀ v x y, r x ≤ r v → r y ≤ r v → H.Adj v x → H.Adj v y → x ≠ y → H.Adj x y

theorem fan (r : W → ℕ) (hr : Eliminates H r) {n : ℕ} {p : ℕ → W}
    (hp : InducedPath H p n) {v : W} (hv : ∀ i ≤ n, v ≠ p i)
    (h0 : H.Adj v (p 0)) (hn : H.Adj v (p n)) :
    ∀ i ≤ n, H.Adj v (p i) := by
  induction n generalizing p with
  | zero => intro i hi; simpa only [show i = 0 by omega] using h0
  | succ n ih =>
    obtain ⟨k,hk,hm⟩ := (Finset.range (n+2)).exists_max_image (fun i => r (p i)) (by simp)
    have hkn : k ≤ n+1 := by have := Finset.mem_range.mp hk; omega
    have hmax : ∀ i ≤ n+1, r (p i) ≤ r (p k) := fun i hi => hm i (Finset.mem_range.mpr (by omega))
    have hends : k = 0 ∨ k = n+1 := by
      by_contra h
      have hk0 : 0 < k := by omega
      have hkl : k < n+1 := by omega
      have hleft : H.Adj (p k) (p (k-1)) := by
        simpa only [Nat.sub_add_cancel hk0] using (hp.step (k-1) (by omega)).symm
      have hright := hp.step k hkl
      have he := hr (p k) (p (k-1)) (p (k+1)) (hmax _ (by omega)) (hmax _ (by omega))
        hleft hright (fun he => by have := hp.inj _ (by omega) _ (by omega) he; omega)
      exact hp.no_chord (k-1) (k+1) (by omega) (by omega) he
    by_cases hrv : r (p k) ≤ r v
    · have he := hr v (p 0) (p (n+1)) ((hmax 0 (by omega)).trans hrv)
        ((hmax (n+1) (by omega)).trans hrv) h0 hn
        (fun he => by have := hp.inj 0 (by omega) (n+1) (by omega) he; omega)
      have hn0 : n = 0 := by
        by_contra hn0
        exact hp.no_chord 0 (n+1) (by omega) (by omega) he
      subst n
      intro i hi
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · exact h0
      · exact hn
    · have hrv : r v ≤ r (p k) := by omega
      rcases hends with rfl | rfl
      · have h1 := hr (p 0) v (p 1) hrv (hmax 1 (by omega)) h0.symm
          (hp.step 0 (by omega)) (hv 1 (by omega))
        have htail : InducedPath H (fun i => p (i+1)) n :=
          ⟨fun i hi j hj he => by have := hp.inj (i+1) (by omega) (j+1) (by omega) he; omega,
           fun i hi => hp.step (i+1) (by omega),
           fun i j hij hj => hp.no_chord (i+1) (j+1) (by omega) (by omega)⟩
        have hall := ih htail (fun i hi => hv (i+1) (by omega)) h1 hn
        intro i hi
        by_cases hi0 : i = 0
        · simpa [hi0] using h0
        · simpa only [Nat.sub_add_cancel (show 1 ≤ i by omega)] using hall (i-1) (by omega)
      · have hlast := hr (p (n+1)) v (p n) hrv (hmax n (by omega)) hn.symm
          (hp.step n (by omega)).symm (hv n (by omega))
        have hinit : InducedPath H p n :=
          ⟨fun i hi j hj => hp.inj i (by omega) j (by omega),
           fun i hi => hp.step i (by omega),
           fun i j hij hj => hp.no_chord i j hij (by omega)⟩
        have hall := ih hinit (fun i hi => hv i (by omega)) h0 hlast
        intro i hi
        by_cases hin : i ≤ n
        · exact hall i hin
        · simpa only [show i = n+1 by omega] using hn

theorem shortest_induced {x y : W} (p : H.Walk x y) (hp : p.length = H.dist x y) :
    InducedPath H p.getVert p.length := by
  refine ⟨fun i hi j hj he => (p.isPath_of_length_eq_dist hp).getVert_injOn hi hj he,
    fun i hi => p.adj_getVert_succ hi, ?_⟩
  intro i j hij hj hadj
  have hb := H.dist_le ((p.take i).append (hadj.toWalk.append (p.drop j)))
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hb
  rw [← hp] at hb
  omega

/-- Indexed induced cycles in a graph with this elimination rank are triangles. -/
theorem induced_cycle_triangle (r : W → ℕ) (hr : Eliminates H r)
    {n : ℕ} (hn : 3 ≤ n) (p : ℕ → W)
    (hinj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (hstep : ∀ i < n-1, H.Adj (p i) (p (i+1)))
    (hclose : H.Adj (p 0) (p (n-1)))
    (hchord : ∀ i j, i+1 < j → j < n → (i ≠ 0 ∨ j ≠ n-1) → ¬ H.Adj (p i) (p j)) :
    n = 3 := by
  have hp : InducedPath H (fun i => p (i+1)) (n-2) :=
    ⟨fun i hi j hj he => by have := hinj (i+1) (by omega) (j+1) (by omega) he; omega,
     fun i hi => hstep (i+1) (by omega),
     fun i j hij hj => hchord (i+1) (j+1) (by omega) (by omega) (Or.inl (by omega))⟩
  have hf := fan r hr hp (v := p 0)
    (fun i hi he => by have := hinj 0 (by omega) (i+1) (by omega) he; omega)
    (hstep 0 (by omega)) (by simpa [show n-2+1 = n-1 by omega] using hclose)
  by_contra hne
  exact hchord 0 2 (by omega) (by omega) (Or.inr (by omega)) (hf 1 (by omega))

end ChordalFan

theorem forest_L2_eliminates {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic) :
    ChordalFan.Eliminates (L2 G) (ForestL2.height G) :=
  fun _ _ _ => ForestL2.lower_neighbours_clique hG

theorem forest_L2_chordal {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {n : ℕ} (hn : 3 ≤ n) (p : ℕ → G.edgeSet)
    (hinj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (hstep : ∀ i < n-1, (L2 G).Adj (p i) (p (i+1)))
    (hclose : (L2 G).Adj (p 0) (p (n-1)))
    (hchord : ∀ i j, i+1 < j → j < n → (i ≠ 0 ∨ j ≠ n-1) →
      ¬ (L2 G).Adj (p i) (p j)) : n = 3 :=
  ChordalFan.induced_cycle_triangle _ (forest_L2_eliminates hG) hn p hinj hstep hclose hchord

end Se20Part
