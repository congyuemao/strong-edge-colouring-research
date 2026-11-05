module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Tauto

/-!
A first formalisation layer for the induced-matching packing project.

Core definitions and the private-clique exchange lemma, typechecked with
the pinned Lean/mathlib toolchain. Conflicts use the *whole* source graph,
including edges outside the candidate set. This module does not establish
the unconditional 20-packing theorem; see README.md for the verified scope.
-/

@[expose] public section

namespace Se20Part.Legacy

universe u

variable {V : Type u}

/-- Two distinct original edges are strongly conflicting when they are
adjacent in the line graph or joined by a length-two line-graph walk.
The intermediate edge is ANY original edge, including one outside F. -/
def StrongConflict (G : SimpleGraph V) (e f : G.edgeSet) : Prop :=
  e ≠ f ∧
    (G.lineGraph.Adj e f ∨
      ∃ g : G.edgeSet, G.lineGraph.Adj e g ∧ G.lineGraph.Adj g f)

theorem strongConflict_symm (G : SimpleGraph V) {e f : G.edgeSet}
    (h : StrongConflict G e f) : StrongConflict G f e := by
  rcases h with ⟨hne, hconf⟩
  refine ⟨hne.symm, ?_⟩
  rcases hconf with hadj | ⟨g, heg, hgf⟩
  · exact Or.inl (G.lineGraph.adj_symm hadj)
  · exact Or.inr ⟨g, G.lineGraph.adj_symm hgf, G.lineGraph.adj_symm heg⟩

theorem strongConflict_irrefl (G : SimpleGraph V) (e : G.edgeSet) :
    ¬ StrongConflict G e e := by
  intro h
  exact h.1 rfl

/-- Conflict graph of ALL edges of the original graph. -/
def conflictGraph (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj := StrongConflict G
  symm := ⟨by
    intro e f h
    exact strongConflict_symm G h⟩
  loopless := ⟨by
    intro e h
    exact strongConflict_irrefl G e h⟩

/-- The conflict graph restricted to selected edges, while retaining
all original edges as witnesses for conflict. -/
def candidateConflictGraph (G : SimpleGraph V)
    (F : Set G.edgeSet) : SimpleGraph F :=
  (conflictGraph G).induce F

instance candidateConflictGraph_decidableRel (G : SimpleGraph V)
    [DecidableRel (conflictGraph G).Adj] (F : Set G.edgeSet) :
    DecidableRel (candidateConflictGraph G F).Adj := fun e f =>
  inferInstanceAs (Decidable ((conflictGraph G).Adj e.val f.val))

theorem candidateConflictGraph_adj_iff (G : SimpleGraph V)
    (F : Set G.edgeSet) (e f : F) :
    (candidateConflictGraph G F).Adj e f ↔
      StrongConflict G (e : G.edgeSet) (f : G.edgeSet) := by
  rfl

/-- `x` is covered uniquely by `v` among selected independent vertices,
using closed neighbourhoods. -/
def IsPrivate {W : Type*} (H : SimpleGraph W) (M : Finset W)
    (v x : W) : Prop :=
  (x = v ∨ H.Adj x v) ∧
    ∀ w ∈ M, w ≠ v → x ≠ w ∧ ¬ H.Adj x w

theorem private_centre {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (M : Finset W) (v : W)
    (hM : H.IsMaximumIndepSet M) (hv : v ∈ M) :
    IsPrivate H M v v := by
  constructor
  · exact Or.inl rfl
  · intro w hw hwne
    constructor
    · exact hwne.symm
    · exact hM.isIndepSet hv hw hwne.symm

/-- Exchange lemma: the vertices whose closed neighbourhood meets
`M` exactly at `v` must form a clique. -/
theorem private_isClique {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (M : Finset W) (v : W)
    (hM : H.IsMaximumIndepSet M) (hv : v ∈ M) :
    H.IsClique {x : W | IsPrivate H M v x} := by
  intro x hx y hy hxy
  change IsPrivate H M v x at hx
  change IsPrivate H M v y at hy
  by_cases hxv : x = v
  · subst x
    rcases hy.1 with hyv | hyv
    · exact (hxy hyv.symm).elim
    · exact H.adj_symm hyv
  by_cases hyv : y = v
  · subst y
    rcases hx.1 with hx' | hx'
    · exact (hxv hx').elim
    · exact hx'
  have hxout : x ∉ M := by
    intro hxm
    exact (hx.2 x hxm hxv).1 rfl
  have hyout : y ∉ M := by
    intro hym
    exact (hy.2 y hym hyv).1 rfl
  by_contra hno
  let T : Finset W := insert x (insert y (M.erase v))
  have hTI : H.IsIndepSet (↑T : Set W) := by
    intro a ha b hb hab
    change a ∈ T at ha
    change b ∈ T at hb
    simp only [T, Finset.mem_insert, Finset.mem_erase] at ha hb
    rcases ha with hax | hay | ⟨han, ham⟩
    · subst a
      rcases hb with hbx | hby | ⟨hbn, hbm⟩
      · subst b
        exact (hab rfl).elim
      · subst b
        exact hno
      · exact (hx.2 b hbm hbn).2
    · subst a
      rcases hb with hbx | hby | ⟨hbn, hbm⟩
      · subst b
        intro hyx
        exact hno (H.adj_symm hyx)
      · subst b
        exact (hab rfl).elim
      · exact (hy.2 b hbm hbn).2
    · rcases hb with hbx | hby | ⟨hbn, hbm⟩
      · subst b
        intro hax
        exact (hx.2 a ham han).2 (H.adj_symm hax)
      · subst b
        intro hay
        exact (hy.2 a ham han).2 (H.adj_symm hay)
      · exact hM.isIndepSet ham hbm hab
  have hxni : x ∉ insert y (M.erase v) := by
    simp only [Finset.mem_insert]
    rintro (heq | heq)
    · exact hxy heq
    · exact hxout (Finset.mem_erase.mp heq).2
  have hyni : y ∉ M.erase v := by
    intro h
    exact hyout (Finset.mem_erase.mp h).2
  have hc1 : (insert x (insert y (M.erase v))).card =
      (insert y (M.erase v)).card + 1 :=
    Finset.card_insert_of_notMem hxni
  have hc2 : (insert y (M.erase v)).card = (M.erase v).card + 1 :=
    Finset.card_insert_of_notMem hyni
  have hc3 : (M.erase v).card + 1 = M.card :=
    Finset.card_erase_add_one hv
  have hcT : T.card = M.card + 1 := by
    change (insert x (insert y (M.erase v))).card = M.card + 1
    omega
  have hmax := hM.maximum T hTI
  omega

/-- The final elementary arithmetic conversion, once the substantial
combinatorial double count and the local upper bound are available. -/
theorem twenty_packing_arithmetic (n k terms : ℕ)
    (hcount : 2 * n ≤ terms) (hloc : terms ≤ 40 * k) :
    n ≤ 20 * k := by
  omega

end Se20Part.Legacy
