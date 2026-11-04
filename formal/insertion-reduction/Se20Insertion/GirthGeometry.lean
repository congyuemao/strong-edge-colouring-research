import Se20Insertion.Triangle
import Mathlib.Combinatorics.SimpleGraph.Girth

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace GirthGeometry
variable {V : Type*} {G : SimpleGraph V}

/-- We use Mathlib's extended girth, whose value on a forest is infinity. -/
theorem no_short_cycle (hg : 7 ≤ G.egirth) {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (hlen : p.length ≤ 6) : False := by
  have hh := hg.trans hp.egirth_le_length
  have : 7 ≤ p.length := by exact_mod_cast hh
  omega

theorem no_triangle (hg : 7 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  apply no_short_cycle hg p _ (by simp [p])
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [p, SimpleGraph.Walk.isPath_def, hbc.ne, hca.ne, Ne.symm hab.ne]

theorem square_backtrack (hg : 7 ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    a = c ∨ b = d := by
  by_contra! hn
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  apply no_short_cycle hg p _ (by simp [p])
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [p, SimpleGraph.Walk.isPath_def, hbc.ne, hcd.ne, hda.ne,
    Ne.symm hab.ne, hn.2, Ne.symm hn.1]

theorem pentagon_backtrack (hg : 7 ≤ G.egirth) {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) :
    a = c ∨ b = d ∨ c = e ∨ d = a ∨ e = b := by
  by_contra! hn
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil))))
  apply no_short_cycle hg p _ (by simp [p])
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [p, SimpleGraph.Walk.isPath_def, hbc.ne, hcd.ne, hde.ne, hea.ne,
    Ne.symm hab.ne, hn.2.1, hn.2.2.1, hn.2.2.2.1,
    Ne.symm hn.1, Ne.symm hn.2.2.2.2]

theorem hexagon_backtrack (hg : 7 ≤ G.egirth) {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a) :
    a = c ∨ b = d ∨ c = e ∨ d = f ∨ e = a ∨ f = b := by
  by_contra! hn
  have had : a ≠ d := by intro h; subst d; exact no_triangle hg hab hbc hcd
  have hbe : b ≠ e := by intro h; subst e; exact no_triangle hg hbc hcd hde
  have hcf : c ≠ f := by intro h; subst f; exact no_triangle hg hcd hde hef
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef (.cons hfa .nil)))))
  apply no_short_cycle hg p _ (by simp [p])
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [p, SimpleGraph.Walk.isPath_def, hbc.ne, hcd.ne, hde.ne, hef.ne, hfa.ne,
    Ne.symm hab.ne, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
    Ne.symm hn.1, Ne.symm hn.2.2.2.2.2, hbe, hcf, Ne.symm had]

/-- Endpoint formulation of membership in a closed conflict neighbourhood. -/
def Close (a b c d : V) : Prop :=
  a = c ∨ a = d ∨ b = c ∨ b = d ∨
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

theorem close_of_conflict {e f : G.edgeSet} {a b c d : V}
    (he : e.val = s(a,b)) (hf : f.val = s(c,d))
    (h : e = f ∨ (L2 G).Adj e f) : Close (G := G) a b c d := by
  rcases h with h | ⟨_, x, hx, y, hy, hxy⟩
  · have hh : a ∈ f.val := h ▸ (he ▸ Sym2.mem_mk_left a b)
    simp only [hf, Sym2.mem_iff] at hh
    unfold Close
    tauto
  · simp only [he, Sym2.mem_iff] at hx
    simp only [hf, Sym2.mem_iff] at hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      rcases hxy with hxy | hxy <;> simp_all [Close]

theorem common_near_endpoints (hg : 7 ≤ G.egirth) {a b c x y : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c) (hxy : G.Adj x y)
    (h1 : Close (G := G) a b x y) (h2 : Close (G := G) a c x y) :
    a = x ∨ a = y ∨ b = x ∨ b = y ∨ G.Adj a x ∨ G.Adj a y := by
  simp only [Close] at h1 h2
  grind (instances := 10000) only [SimpleGraph.Adj.ne, → SimpleGraph.Adj.symm, → no_triangle, → square_backtrack, → pentagon_backtrack]

theorem common_far_endpoints (hg : 7 ≤ G.egirth) {a b c d x y : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hcd : G.Adj c d)
    (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hxy : G.Adj x y)
    (h1 : Close (G := G) a b x y) (h2 : Close (G := G) c d x y) :
    a = x ∨ a = y ∨ c = x ∨ c = y := by
  simp only [Close] at h1 h2
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
    grind (instances := 2000) only [SimpleGraph.Adj.ne, → SimpleGraph.Adj.symm,
      → no_triangle, → square_backtrack, → pentagon_backtrack, → hexagon_backtrack]

theorem opposite_near_endpoints (hg : 7 ≤ G.egirth) {a b x y : V}
    (hab : G.Adj a b) (hxy : G.Adj x y)
    (h1 : a = x ∨ a = y ∨ b = x ∨ b = y ∨ G.Adj a x ∨ G.Adj a y)
    (h2 : b = x ∨ b = y ∨ a = x ∨ a = y ∨ G.Adj b x ∨ G.Adj b y) :
    a = x ∨ a = y ∨ b = x ∨ b = y := by
  grind (instances := 10000) only [SimpleGraph.Adj.ne, → SimpleGraph.Adj.symm, → no_triangle, → square_backtrack]

end GirthGeometry
end Se20Insertion
