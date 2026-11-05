import Se20Insertion.LowDegree

noncomputable section
open scoped Classical
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

/-- The actual extension, with the old colour function retained off U. -/
def fillLists (φ : PartialColouring H F) (U : Finset W)
    (c : U → Colour) (hinj : Function.Injective c)
    (hfree : ∀ x : U, φ.Free x.val (c x)) : PartialColouring H (F ∪ U) where
  colour x := if hx : x ∈ U then c ⟨x,hx⟩ else φ.colour x
  proper := by
    intro x y hx hy hxy heq
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · have hc : c ⟨x,hxU⟩ = c ⟨y,hyU⟩ := by simpa [hxU,hyU] using heq
      exact hxy.ne (congrArg Subtype.val (hinj hc))
    · exact hfree ⟨x,hxU⟩ ⟨y, (Finset.mem_union.mp hy).resolve_right hyU, hxy,
        by simpa [hxU,hyU] using heq.symm⟩
    · exact hfree ⟨y,hyU⟩ ⟨x, (Finset.mem_union.mp hx).resolve_right hxU, hxy.symm,
        by simpa [hxU,hyU] using heq⟩
    · exact φ.proper ((Finset.mem_union.mp hx).resolve_right hxU)
        ((Finset.mem_union.mp hy).resolve_right hyU) hxy (by simpa [hxU,hyU] using heq)

theorem fillLists_agrees (φ : PartialColouring H F) (U : Finset W)
    (c : U → Colour) (hinj : Function.Injective c)
    (hfree : ∀ x : U, φ.Free x.val (c x)) (hdis : Disjoint F U) :
    ∀ x ∈ F, (φ.fillLists U c hinj hfree).colour x = φ.colour x := by
  intro x hx
  have hxU : x ∉ U := fun h => Finset.disjoint_left.mp hdis hx h
  simp [fillLists,hxU]

end Se20Insertion.PartialColouring

namespace Se20Insertion

/-- Lemma 11.24(1) with direct extension recorded explicitly: every old
colour is preserved. The obstruction is a common two-element list. -/
theorem degree_three_direct_extension {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (u : V) (hu : G.degree u = 3)
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (hF : Disjoint F (incident G u))
    (hnot : ¬ ∃ S : Finset Colour, S.card = 2 ∧ ∀ e ∈ incident G u, φ.available e = S) :
    ∃ ψ : PartialColouring (L2 G) (F ∪ incident G u), ∀ x ∈ F, ψ.colour x = φ.colour x := by
  have hL := (degree_three_lists G hΔ u hu φ hF).1
  have hn : Fintype.card (incident G u) = 3 := by rw [Fintype.card_coe,card_incident,hu]
  haveI : Nonempty (incident G u) := Fintype.card_pos_iff.mp (by omega)
  have hex : ∃ c : incident G u → Colour, Function.Injective c ∧
      ∀ e, c e ∈ φ.available e.val := by
    by_contra hno
    obtain ⟨S,hS,heq⟩ := almost_full_lists (fun e : incident G u => φ.available e.val)
      (by intro e; rw [hn]; exact hL e.val e.property) hno
    exact hnot ⟨S,by rw [hn] at hS; exact hS, fun e he => heq ⟨e,he⟩⟩
  obtain ⟨c,hc,hfree⟩ := hex
  have hf : ∀ e : incident G u, φ.Free e.val (c e) :=
    fun e => (Finset.mem_filter.mp (hfree e)).2
  exact ⟨φ.fillLists (incident G u) c hc hf, φ.fillLists_agrees _ c hc hf hF⟩

end Se20Insertion
