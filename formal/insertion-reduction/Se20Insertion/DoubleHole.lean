import Se20Insertion.HoleMoves

noncomputable section
open scoped Classical

namespace Se20Insertion.PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- The configuration is read entirely in the original colouring. In particular
`g` need not be a hole, and no reachability assertion is included. -/
def DoubleHoleConfig (φ : PartialColouring H F) (g f w : W) : Prop :=
  f ∈ F ∧ w ∈ F ∧ H.Adj g f ∧ H.Adj f w ∧ g ≠ w ∧ ¬ H.Adj g w ∧
    φ.Single g (φ.colour f) f ∧ φ.Single w (φ.colour f) f ∧
      φ.Single f (φ.colour w) w

/-- The double hole move, with precisely the three singleness conditions.
The construction colours `g,w` with the old colour of `f`, and `f` with the
old colour of `w`. It works for every simple graph, hence for every `L2 G`. -/
theorem doubleHoleMove (φ : PartialColouring H F) {g f w : W}
    (_hg : g ∉ F) (hf : f ∈ F) (hw : w ∈ F)
    (hgf : H.Adj g f) (hfw : H.Adj f w) (hgw : g ≠ w) (hngw : ¬ H.Adj g w)
    (hsg : φ.Single g (φ.colour f) f)
    (hsw : φ.Single w (φ.colour f) f)
    (hsf : φ.Single f (φ.colour w) w) :
    Nonempty (PartialColouring H (insert g F)) := by
  classical
  let c : W → Colour := fun x =>
    if x = g then φ.colour f else if x = f then φ.colour w
      else if x = w then φ.colour f else φ.colour x
  have hfg : f ≠ g := hgf.ne.symm
  have hwg : w ≠ g := hgw.symm
  have hwf : w ≠ f := hfw.ne.symm
  have hcol : φ.colour f ≠ φ.colour w := φ.proper hf hw hfw
  have cg : c g = φ.colour f := by simp [c]
  have cf : c f = φ.colour w := by simp [c, hfg]
  have cw : c w = φ.colour f := by simp [c, hwg, hwf]
  have old : ∀ x, x ≠ g → x ≠ f → x ≠ w → c x = φ.colour x := by
    intro x hxg hxf hxw
    simp [c, hxg, hxf, hxw]
  have atg : ∀ x ∈ insert g F, H.Adj g x → c g ≠ c x := by
    intro x hx hadj heq
    have hxg : x ≠ g := hadj.ne.symm
    have hxF := (Finset.mem_insert.mp hx).resolve_left hxg
    by_cases hxf : x = f
    · subst x; exact hcol (by simpa [cg, cf] using heq)
    by_cases hxw : x = w
    · subst x; exact hngw hadj
    exact hxf (hsg.2 x ⟨hxF, hadj, by simpa [cg, old x hxg hxf hxw] using heq.symm⟩)
  have atf : ∀ x ∈ insert g F, H.Adj f x → c f ≠ c x := by
    intro x hx hadj heq
    by_cases hxg : x = g
    · subst x; exact atg f (Finset.mem_insert_of_mem hf) hadj.symm heq.symm
    have hxf : x ≠ f := hadj.ne.symm
    by_cases hxw : x = w
    · subst x; exact hcol (by simpa [cf, cw] using heq.symm)
    exact hxw (hsf.2 x ⟨(Finset.mem_insert.mp hx).resolve_left hxg, hadj,
      by simpa [cf, old x hxg hxf hxw] using heq.symm⟩)
  have atw : ∀ x ∈ insert g F, H.Adj w x → c w ≠ c x := by
    intro x hx hadj heq
    by_cases hxg : x = g
    · subst x; exact hngw hadj.symm
    by_cases hxf : x = f
    · subst x; exact atf w (Finset.mem_insert_of_mem hw) hadj.symm heq.symm
    have hxw : x ≠ w := hadj.ne.symm
    exact hxf (hsw.2 x ⟨(Finset.mem_insert.mp hx).resolve_left hxg, hadj,
      by simpa [cw, old x hxg hxf hxw] using heq.symm⟩)
  refine ⟨⟨c, ?_⟩⟩
  intro x y hx hy hadj
  by_cases hxg : x = g
  · subst x; exact atg y hy hadj
  by_cases hxf : x = f
  · subst x; exact atf y hy hadj
  by_cases hxw : x = w
  · subst x; exact atw y hy hadj
  by_cases hyg : y = g
  · subst y; exact (atg x hx hadj.symm).symm
  by_cases hyf : y = f
  · subst y; exact (atf x hx hadj.symm).symm
  by_cases hyw : y = w
  · subst y; exact (atw x hx hadj.symm).symm
  rw [old x hxg hxf hxw, old y hyg hyf hyw]
  exact φ.proper ((Finset.mem_insert.mp hx).resolve_left hxg)
    ((Finset.mem_insert.mp hy).resolve_left hyg) hadj

theorem DoubleHoleConfig.insert (φ : PartialColouring H F) {g f w : W}
    (hc : φ.DoubleHoleConfig g f w) (hg : g ∉ F) :
    Nonempty (PartialColouring H (insert g F)) :=
  φ.doubleHoleMove hg hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2

end Se20Insertion.PartialColouring
