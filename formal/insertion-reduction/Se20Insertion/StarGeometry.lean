import Se20Insertion.RimCounting
import Se20Insertion.SwapCriteria

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Edges at v other than uv; defined even when uv is absent. -/
def branch (u v : V) : Finset G.edgeSet := incident G v \ incident G u

/-- The common inner part seen by the edges of the star at u. -/
def starBase (u : V) : Finset G.edgeSet :=
  (G.neighborFinset u).biUnion (branch G u)

/-- The outer shell on the v side of uv. Overlaps are retained as set unions. -/
def shell (u v : V) : Finset G.edgeSet :=
  ((G.neighborFinset v).erase u).biUnion (branch G v)

theorem branch_card_le (hΔ : MaxDegreeFour G) {u v : V} (h : G.Adj u v) :
    (branch G u v).card ≤ 3 := by
  let e := edge G h
  have hs : branch G u v ⊆ (incident G v).erase e := by
    intro f hf
    obtain ⟨hv, hu⟩ := Finset.mem_sdiff.mp hf
    exact Finset.mem_erase.mpr ⟨fun he => hu (by subst f; simp [e, edge]), hv⟩
  have hc := Finset.card_erase_add_one (show e ∈ incident G v by simp [e, edge])
  rw [card_incident] at hc
  have := Finset.card_le_card hs
  have := hΔ v
  omega

theorem starBase_card_le (hΔ : MaxDegreeFour G) (u : V) :
    (starBase G u).card ≤ 3 * G.degree u := by
  calc
    _ ≤ ∑ v ∈ G.neighborFinset u, (branch G u v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ G.neighborFinset u, 3 := Finset.sum_le_sum (fun v hv =>
      branch_card_le G hΔ ((G.mem_neighborFinset _ _).mp hv))
    _ = _ := by simp [Nat.mul_comm]

theorem shell_card_le (hΔ : MaxDegreeFour G) {u v : V} (h : G.Adj u v) :
    (shell G u v).card ≤ 9 := by
  have hc := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr h.symm)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hd := hΔ v
  calc
    _ ≤ ∑ w ∈ (G.neighborFinset v).erase u, (branch G v w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ (G.neighborFinset v).erase u, 3 := Finset.sum_le_sum (fun w hw =>
      branch_card_le G hΔ ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2))
    _ ≤ 9 := by simp only [Finset.sum_const, smul_eq_mul]; omega

theorem conflicts_star_decomposition (e : G.edgeSet) {u v : V} (he : e.val = s(u,v)) :
    conflicts G e = (incident G u).erase e ∪ starBase G u ∪ shell G u v := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.2)
  have near (w : V) (hw : G.Adj u w) (f : G.edgeSet) (hf : w ∈ f.val)
      (hne : e ≠ f) : (L2 G).Adj e f :=
    ⟨hne, u, he ▸ Sym2.mem_mk_left u v, w, hf, Or.inr hw⟩
  ext f
  rw [conflicts_eq_rim G e he]
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_erase, mem_incident,
    starBase, shell, branch, Finset.mem_sdiff, Finset.mem_biUnion, mem_incident,
    SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨w, hw, hf⟩
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨hwv, huw⟩ := Finset.mem_erase.mp hw
      have huw := (G.mem_neighborFinset _ _).mp huw
      by_cases huf : u ∈ f.val
      · left; left; refine ⟨?_, huf⟩
        intro h; subst f
        rcases (Sym2.mem_iff.mp (he ▸ hf)) with h | h
        · exact huw.ne h.symm
        · exact hwv h
      · exact Or.inl (Or.inr ⟨w, huw, hf, huf⟩)
    · obtain ⟨hwu, hvw⟩ := Finset.mem_erase.mp hw
      have hvw := (G.mem_neighborFinset _ _).mp hvw
      by_cases hvf : v ∈ f.val
      · by_cases huf : u ∈ f.val
        · have hfuv : f.val = s(u,v) := (Sym2.mem_and_mem_iff huv.ne).mp ⟨huf, hvf⟩
          have hfe : f = e := Subtype.ext (hfuv.trans he.symm)
          subst f
          rcases (Sym2.mem_iff.mp (he ▸ hf)) with h | h
          · exact (hwu h).elim
          · exact (hvw.ne h.symm).elim
        · exact Or.inl (Or.inr ⟨v, huv, hvf, huf⟩)
      · exact Or.inr ⟨w, ⟨hwu, hvw⟩, hf, hvf⟩
  · intro hf
    have hadj : (L2 G).Adj e f := by
      rcases hf with (⟨hne, hu⟩ | ⟨w, hw, hf, hu⟩) | ⟨w, ⟨hwu, hvw⟩, hf, hv⟩
      · exact ⟨hne.symm, u, he ▸ Sym2.mem_mk_left u v, u, hu, Or.inl rfl⟩
      · exact near w hw f hf (fun h => hu (h ▸ (he ▸ Sym2.mem_mk_left u v)))
      · exact ⟨(fun h => hv (h ▸ (he ▸ Sym2.mem_mk_right u v))), v,
          he ▸ Sym2.mem_mk_right u v, w, hf, Or.inr hvw⟩
    have hm := (mem_conflicts G e f).mpr hadj
    rw [conflicts_eq_rim G e he] at hm
    simpa only [Finset.mem_biUnion, mem_incident] using hm

theorem shell_conflicts_branch {u v : V} (huv : G.Adj u v)
    {f g : G.edgeSet} (hf : f ∈ shell G u v) (hg : v ∈ g.val) (hne : g ≠ f) :
    (L2 G).Adj g f := by
  obtain ⟨w, hw, hf⟩ := Finset.mem_biUnion.mp hf
  exact ⟨hne, v, hg, w, (mem_incident G w f).mp (Finset.mem_sdiff.mp hf).1,
    Or.inr ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2)⟩

end Se20Insertion
