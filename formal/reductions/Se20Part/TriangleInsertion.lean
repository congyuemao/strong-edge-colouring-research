import Se20Part.Triangle

noncomputable section
open scoped Classical
namespace Se20Part
namespace PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

theorem insertFree_unchanged (φ : PartialColouring H F) {e : W} {a : Colour}
    (he : e ∉ F) (ha : φ.Free e a) :
    ∀ x ∈ F, (φ.insertFree e a ha).colour x = φ.colour x := by
  intro x hx
  have hxe : x ≠ e := fun h => he (h ▸ hx)
  simp [insertFree, hxe]

/-- A single free recolouring followed by insertion, with an explicit bound
on the number of previously coloured edges changed. -/
theorem single_free_insertion (φ : PartialColouring H F) {e f : W} {p q : Colour}
    (he : e ∉ F) (hs : φ.Single e p f) (hqp : q ≠ p) (hq : φ.Free f q) :
    ∃ ψ : PartialColouring H (insert e F),
      (F.filter (fun x => ψ.colour x ≠ φ.colour x)).card ≤ 1 := by
  have hind : ∀ x ∈ ({f} : Set W), ∀ y ∈ ({f} : Set W), ¬ H.Adj x y := by
    simp
  have hfree : ∀ x ∈ ({f} : Set W), φ.Free x q := by simpa using hq
  let θ := φ.recolour {f} q hind hfree
  have hefree : θ.Free e p := by
    rintro ⟨x, hxF, hex, hc⟩
    simp only [θ, recolour, Set.mem_singleton_iff] at hc
    by_cases hxf : x = f
    · exact hqp (by simpa [hxf] using hc)
    · have hcol : φ.colour x = p := by simpa [hxf] using hc
      exact hxf (hs.2 x ⟨hxF, hex, hcol⟩)
  let ψ := θ.insertFree e p hefree
  refine ⟨ψ, ?_⟩
  have hsub : F.filter (fun x => ψ.colour x ≠ φ.colour x) ⊆ {f} := by
    intro x hx
    obtain ⟨hxF, hxcol⟩ := Finset.mem_filter.mp hx
    by_contra hxf
    have hxf' : x ≠ f := by simpa using hxf
    apply hxcol
    rw [θ.insertFree_unchanged he hefree x hxF]
    simp [θ, recolour, hxf']
  simpa using Finset.card_le_card hsub

end PartialColouring

/-- Lemma 11.17, including the promised at-most-one recolouring. -/
theorem triangle_insertion {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (e : G.edgeSet) (he : e ∉ F) (ht : OnTriangle G e) :
    ∃ ψ : PartialColouring (L2 G) (insert e F),
      (F.filter (fun f => ψ.colour f ≠ φ.colour f)).card ≤ 1 := by
  rcases triangle_local_repair G hΔ φ e he ht with ⟨c, hc⟩ | ⟨p, f, q, hs, hqp, hq⟩
  · refine ⟨φ.insertFree e c hc, ?_⟩
    have hempty : F.filter (fun f => (φ.insertFree e c hc).colour f ≠ φ.colour f) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      exact (Finset.mem_filter.mp hf).2 (φ.insertFree_unchanged he hc f (Finset.mem_filter.mp hf).1)
    simp [hempty]
  · exact φ.single_free_insertion he hs hqp hq

/-- Lemma 11.36, in the equivalent partial-colouring representation. -/
theorem triangle_edges_last {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hΔ : MaxDegreeFour G) (F T : Finset G.edgeSet) (hTF : T ⊆ F)
    (hT : ∀ e ∈ T, OnTriangle G e)
    (hc : Nonempty (PartialColouring (L2 G) (F \ T))) :
    Nonempty (PartialColouring (L2 G) F) := by
  induction T using Finset.induction_on with
  | empty => simpa using hc
  | @insert e T heT ih =>
    obtain ⟨φ⟩ := hc
    have heF := hTF (Finset.mem_insert_self e T)
    obtain ⟨ψ, _⟩ := triangle_insertion G hΔ φ e (by simp) (hT e (Finset.mem_insert_self e T))
    have heq : insert e (F \ insert e T) = F \ T := by
      ext f
      by_cases hfe : f = e
      · subst f; simp [heF, heT]
      · simp [hfe]
    apply ih (fun f hf => hTF (Finset.mem_insert_of_mem hf))
      (fun f hf => hT f (Finset.mem_insert_of_mem hf))
    exact ⟨heq ▸ ψ⟩

end Se20Part
