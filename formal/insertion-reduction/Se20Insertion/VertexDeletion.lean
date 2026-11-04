import Se20Insertion.Exceptional

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem exists_induced_edge (S : Set V) (e : G.edgeSet)
    (he : ∀ x ∈ e.val, x ∈ S) :
    ∃ f : (G.induce S).edgeSet, (inducedEmbedding G S).mapEdgeSet f = e := by
  obtain ⟨u, v, huv⟩ : ∃ u v, e.val = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e.val
  have hu : u ∈ S := he u (huv ▸ Sym2.mem_mk_left u v)
  have hv : v ∈ S := he v (huv ▸ Sym2.mem_mk_right u v)
  have hadj : G.Adj u v := G.mem_edgeSet.mp (huv ▸ e.2)
  refine ⟨⟨s((⟨u, hu⟩ : S), (⟨v, hv⟩ : S)), hadj⟩, ?_⟩
  apply Subtype.ext
  exact huv.symm

/-- A strong colouring after vertex deletion is a partial colouring of the
original graph on exactly the complement of the deleted star. -/
theorem starColouring_of_deleteColourable (v : V)
    (hc : StrongColourable (G.induce {x | x ≠ v}) 20) :
    Nonempty (PartialColouring (L2 G) (Finset.univ \ incident G v)) := by
  obtain ⟨c⟩ := hc
  have hex : ∀ e : G.edgeSet, v ∉ e.val →
      ∃ f : (G.induce {x | x ≠ v}).edgeSet,
        (inducedEmbedding G {x | x ≠ v}).mapEdgeSet f = e := by
    intro e he
    apply exists_induced_edge G _ e
    intro x hx hxe
    exact he (hxe ▸ hx)
  let inv (e : G.edgeSet) (he : v ∉ e.val) := (hex e he).choose
  have hinv (e : G.edgeSet) (he : v ∉ e.val) :
      (inducedEmbedding G {x | x ≠ v}).mapEdgeSet (inv e he) = e := (hex e he).choose_spec
  refine ⟨⟨fun e => if he : v ∉ e.val then c (inv e he) else 0, ?_⟩⟩
  intro e f he hf hef
  have he' : v ∉ e.val := by simpa using he
  have hf' : v ∉ f.val := by simpa using hf
  simp only [dite_eq_left he', dite_eq_left hf']
  apply c.valid
  apply (L2_induce_adj_iff G {x | x ≠ v} _ _).mp
  rw [hinv e he', hinv f hf']
  exact hef

/-- Fill a star, handling triangle edges before invoking the restricted
insertion hypothesis. Every intermediate colouring still uses `L2 G`. -/
theorem fill_star_fin (h : StarInsertion) {n : ℕ} (G : SimpleGraph (Fin n))
    (hreg : FourRegular G) (v : Fin n) (hv : Nonexceptional G v)
    (U : Finset G.edgeSet) (hU : ∀ e ∈ U, v ∈ e.val)
    (hc : Nonempty (PartialColouring (L2 G) (Finset.univ \ U))) : StrongColourable G 20 := by
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hUempty : U = ∅
    · subst U
      obtain ⟨φ⟩ := hc
      have hc' : Nonempty (PartialColouring (L2 G) Finset.univ) := by simpa using Nonempty.intro φ
      obtain ⟨φ'⟩ := hc'
      exact ⟨SimpleGraph.Coloring.mk φ'.colour (fun {x y} hxy =>
        φ'.proper (Finset.mem_univ _) (Finset.mem_univ _) hxy)⟩
    obtain ⟨φ⟩ := hc
    have step : ∃ e ∈ U, Nonempty (PartialColouring (L2 G) (insert e (Finset.univ \ U))) := by
      by_cases ht : ∃ e ∈ U, OnTriangle G e
      · obtain ⟨e, he, ht⟩ := ht
        obtain ⟨ψ, _⟩ := triangle_insertion G (fun v => (hreg v).le) φ e (by simp [he]) ht
        refine ⟨e, he, ⟨{ colour := ψ.colour, proper := ?_ }⟩⟩
        intro x y hx hy hxy
        exact ψ.proper (by simpa using hx) (by simpa using hy) hxy
      · exact h n G hreg v hv U ⟨Finset.nonempty_iff_ne_empty.mpr hUempty, hU⟩
          (by simpa using ht) φ
    obtain ⟨e, he, ψ⟩ := step
    apply ih (U.erase e) (Finset.erase_ssubset he)
      (fun f hf => hU f (Finset.mem_of_mem_erase hf))
    have heq : insert e (Finset.univ \ U) = Finset.univ \ U.erase e := by
      ext f
      by_cases hfe : f = e <;> simp [hfe]
    rwa [← heq]

end Se20Insertion
