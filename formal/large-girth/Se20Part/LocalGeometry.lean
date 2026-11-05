import Se20Part.Definitions

noncomputable section
open scoped Classical
namespace Se20Part

/-- The precise short-path uniqueness fact behind the manuscript's local tree arguments. -/
theorem short_paths_unique {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) {u v : V} {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length < g) : p = q := by
  by_contra hne
  obtain ⟨w,_,_,c,hc,hl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hg w c hc
  omega

/-- Lemma 3.15, step 1: every simple path shorter than half the girth is geodesic. -/
theorem short_path_geodesic {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 2 * p.length < g) : p.length = G.dist u v := by
  obtain ⟨q,hq,hd⟩ := p.reachable.exists_path_of_dist
  have hle : q.length ≤ p.length := by rw [hd]; exact G.dist_le p
  have heq := short_paths_unique hg hp hq (by omega)
  simpa [heq] using hd

/-- A parent map covering every edge of a simple path cannot point inward at both ends.
This is the combinatorial coordination step used by the tree/pseudoforest argument. -/
theorem no_facing_parent_choices {V : Type*} (parent : V → Option V) (v : ℕ → V)
    {n : ℕ} (hn : 2 ≤ n)
    (hinj : Set.InjOn v {i | i ≤ n})
    (hedges : ∀ i < n, parent (v i) = some (v (i+1)) ∨
      parent (v (i+1)) = some (v i))
    (hfirst : parent (v 1) = some (v 0))
    (hlast : parent (v (n-1)) = some (v n)) : False := by
  have hforward : ∀ j, 1 ≤ j → j ≤ n → parent (v j) = some (v (j-1)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hjn
      by_cases hj1 : j = 1
      · simpa [hj1] using hfirst
      · have hj2 : 2 ≤ j := by omega
        have hjback : j-1+1 = j := by omega
        have hprev := ih (j-1) (by omega) (by omega) (by omega)
        rcases hedges (j-1) (by omega) with h | h
        · have hv : v (j-1-1) = v j :=
            Option.some.inj (hprev.symm.trans (by simpa only [hjback] using h))
          have := hinj (by simp; omega) (by simp; omega) hv
          omega
        · simpa only [hjback] using h
  have hv : v (n-1-1) = v n :=
    Option.some.inj ((hforward (n-1) (by omega) (by omega)).symm.trans hlast)
  have := hinj (by simp; omega) (by simp) hv
  omega

end Se20Part
