import Se20Insertion.Triangle
import Se20Insertion.Covering

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V C : Type*} (G : SimpleGraph V) (c : G.edgeSet → C)

def incidentPalette (u : V) : Set C := {a | ∃ e : G.edgeSet, u ∈ e.val ∧ c e = a}

def IncidentProper : Prop :=
  ∀ e f : G.edgeSet, ∀ u, u ∈ e.val → u ∈ f.val → e ≠ f → c e ≠ c f

/-- Section 8.2.2, without the unnecessary four-regularity restriction. -/
theorem strong_iff_incident_palettes :
    (∀ e f, (L2 G).Adj e f → c e ≠ c f) ↔
      IncidentProper G c ∧ ∀ u v (huv : G.Adj u v),
        incidentPalette G c u ∩ incidentPalette G c v = {c (edge G huv)} := by
  constructor
  · intro hc
    refine ⟨fun e f u he hf hne => hc e f ⟨hne,u,he,u,hf,Or.inl rfl⟩,?_⟩
    intro u v huv
    ext a
    constructor
    · rintro ⟨⟨e,he,hce⟩,⟨f,hf,hcf⟩⟩
      have hef : e = f := by
        by_contra hne
        exact hc e f ⟨hne,u,he,v,hf,Or.inr huv⟩ (hce.trans hcf.symm)
      have heq : e = edge G huv := Subtype.ext
        ((Sym2.mem_and_mem_iff huv.ne).mp ⟨he,hef ▸ hf⟩)
      exact (hce.symm.trans (congrArg c heq))
    · intro ha
      change a = c (edge G huv) at ha
      subst a
      exact ⟨⟨edge G huv,by simp [edge],rfl⟩,⟨edge G huv,by simp [edge],rfl⟩⟩
  · rintro ⟨hproper,hpal⟩ e f ⟨hne,u,hu,v,hv,huv⟩ heq
    rcases huv with rfl | huv
    · exact hproper e f u hu hv hne heq
    · have hmem : c e ∈ incidentPalette G c u ∩ incidentPalette G c v :=
        ⟨⟨e,hu,rfl⟩,⟨f,hv,heq.symm⟩⟩
      rw [hpal u v huv] at hmem
      have hce : c e = c (edge G huv) := hmem
      by_cases hek : e = edge G huv
      · exact hproper e f v (by simp [hek,edge]) hv hne heq
      · exact hproper e (edge G huv) u hu (by simp [edge]) hek hce

end Se20Insertion
