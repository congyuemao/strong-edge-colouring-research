import Se20Part.ConflictBounds
import Mathlib.Combinatorics.SimpleGraph.Girth

noncomputable section
open scoped Classical
namespace Se20Part
namespace GirthFive
variable {V : Type*} {G : SimpleGraph V}

/-- We use Mathlib's extended girth, whose value on a forest is infinity. -/
theorem no_short_cycle (hg : 5 ≤ G.egirth) {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (hlen : p.length ≤ 4) : False := by
  have hh := hg.trans hp.egirth_le_length
  have : 5 ≤ p.length := by exact_mod_cast hh
  omega

theorem no_triangle (hg : 5 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  apply no_short_cycle hg p _ (by simp [p])
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [p, SimpleGraph.Walk.isPath_def, hbc.ne, hca.ne, Ne.symm hab.ne]

theorem square_backtrack (hg : 5 ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    a = c ∨ b = d := by
  by_contra! hn
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  apply no_short_cycle hg p _ (by simp [p])
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  simp [p, SimpleGraph.Walk.isPath_def, hbc.ne, hcd.ne, hda.ne,
    Ne.symm hab.ne, hn.2, Ne.symm hn.1]


end GirthFive

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem card_rim_eq_six (h4 : FourRegular G) (hg : 5 ≤ G.egirth)
    {u v : V} (huv : G.Adj u v) : (rim G u v).card = 6 := by
  have hdis : Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hux : G.Adj u x := by simpa using (Finset.mem_erase.mp hx).2
    have hvx : G.Adj v x := by simpa using (Finset.mem_erase.mp hy).2
    exact GirthFive.no_triangle hg huv hvx hux.symm
  have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  have hdu := h4 u
  have hdv := h4 v
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdu hdv
  rw [rim, Finset.card_union_of_disjoint hdis]
  omega

theorem rim_independent (hg : 5 ≤ G.egirth) {u v : V} (huv : G.Adj u v)
    {x y : V} (hx : x ∈ rim G u v) (hy : y ∈ rim G u v) : ¬ G.Adj x y := by
  intro hxy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · have hux : G.Adj u x := by simpa using (Finset.mem_erase.mp hx).2
    have huy : G.Adj u y := by simpa using (Finset.mem_erase.mp hy).2
    exact GirthFive.no_triangle hg hux hxy huy.symm
  · have hux : G.Adj u x := by simpa using (Finset.mem_erase.mp hx).2
    have hvy : G.Adj v y := by simpa using (Finset.mem_erase.mp hy).2
    rcases GirthFive.square_backtrack hg hux hxy hvy.symm huv.symm with h | h
    · exact (Finset.mem_erase.mp hy).1 h.symm
    · exact (Finset.mem_erase.mp hx).1 h
  · have hvx : G.Adj v x := by simpa using (Finset.mem_erase.mp hx).2
    have huy : G.Adj u y := by simpa using (Finset.mem_erase.mp hy).2
    rcases GirthFive.square_backtrack hg hvx hxy huy.symm huv with h | h
    · exact (Finset.mem_erase.mp hy).1 h.symm
    · exact (Finset.mem_erase.mp hx).1 h
  · have hvx : G.Adj v x := by simpa using (Finset.mem_erase.mp hx).2
    have hvy : G.Adj v y := by simpa using (Finset.mem_erase.mp hy).2
    exact GirthFive.no_triangle hg hvx hxy hvy.symm

/-- Section 2's exact degree statement, supplying the geometric hypothesis
for the complete degree-profile classification in Lemma 4.2. -/
theorem L2_degree_eq_twentyFour (h4 : FourRegular G) (hg : 5 ≤ G.egirth)
    (e : G.edgeSet) : (L2 G).degree e = 24 := by
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  have hdis : ((rim G u v : Finset V) : Set V).PairwiseDisjoint (incident G) := by
    intro x hx y hy hne
    apply Finset.disjoint_left.mpr
    intro f hxf hyf
    have hxf : x ∈ f.val := (mem_incident G _ _).mp hxf
    have hyf : y ∈ f.val := (mem_incident G _ _).mp hyf
    obtain ⟨t,hft⟩ := Sym2.mem_iff_exists.mp hxf
    have hyt : y = t := by
      have h := hyf
      rw [hft, Sym2.mem_iff] at h
      exact h.resolve_left hne.symm
    have hxy : G.Adj x y := by
      subst y
      exact G.mem_edgeSet.mp (hft ▸ f.prop)
    exact rim_independent G hg huv hx hy hxy
  have heq : (L2 G).neighborFinset e = conflicts G e := by ext x; simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, heq, conflicts_eq_rim G e he,
    Finset.card_biUnion hdis]
  calc
    _ = ∑ _x ∈ rim G u v, 4 := Finset.sum_congr rfl
      (fun x _ => (card_incident G x).trans (h4 x))
    _ = 24 := by simp [card_rim_eq_six G h4 hg huv]

end Se20Part
