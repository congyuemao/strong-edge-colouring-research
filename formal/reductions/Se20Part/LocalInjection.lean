import Se20Part.GraphBasics

noncomputable section
open scoped Classical
namespace Se20Part
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def LocallyInjective (f : G →g H) : Prop :=
  ∀ v, Set.InjOn f (G.neighborSet v)

theorem local_edge_distinct (f : G →g H) (hf : LocallyInjective f)
    {e k : G.edgeSet} (hek : (L2 G).Adj e k) : f.mapEdgeSet e ≠ f.mapEdgeSet k := by
  obtain ⟨hne,a,ha,b,hb,hab⟩ := hek
  obtain ⟨a',he⟩ := Sym2.mem_iff_exists.mp ha
  obtain ⟨b',hk⟩ := Sym2.mem_iff_exists.mp hb
  have haa' : G.Adj a a' := G.mem_edgeSet.mp (he ▸ e.prop)
  have hbb' : G.Adj b b' := G.mem_edgeSet.mp (hk ▸ k.prop)
  intro hh
  have hpair : s(f a, f a') = s(f b, f b') := by
    simpa only [SimpleGraph.Hom.mapEdgeSet, he, hk, Sym2.map_mk] using
      congrArg Subtype.val hh
  rcases hab with hab | hab
  · subst b
    have hab' : a' = b' := hf a haa' hbb' (Sym2.congr_right.mp hpair)
    apply hne
    apply Subtype.ext
    simpa [he, hk, hab']
  · rcases Sym2.eq_iff.mp hpair with ⟨habf, _⟩ | ⟨hab'f, ha'bf⟩
    · exact (f.map_adj hab).ne habf
    · have hb'a : b' = a := hf b hbb' hab.symm hab'f.symm
      have ha'b : a' = b := hf a haa' hab ha'bf
      apply hne
      apply Subtype.ext
      simp [he, hk, hb'a, ha'b, Sym2.eq_swap]

/-- Local injectivity is enough to preserve distinctness of conflicting edges;
global injectivity of the vertex map is unnecessary. -/
def L2LocalMap (f : G →g H) (hf : LocallyInjective f) : L2 G →g L2 H where
  toFun := f.mapEdgeSet
  map_rel' := by
    intro e k hek
    obtain ⟨hne,a,ha,b,hb,hab⟩ := hek
    refine ⟨local_edge_distinct f hf ⟨hne,a,ha,b,hb,hab⟩, f a,
      Sym2.mem_map.mpr ⟨a,ha,rfl⟩, f b, Sym2.mem_map.mpr ⟨b,hb,rfl⟩, ?_⟩
    exact hab.elim (fun h => Or.inl (congrArg f h)) (fun h => Or.inr (f.map_adj h))

/-- NEW_DIRECTIONS, line 215: pull back any strong edge colouring. -/
theorem strongColourable_pullback (f : G →g H) (hf : LocallyInjective f)
    {k : ℕ} (hc : StrongColourable H k) : StrongColourable G k := by
  obtain ⟨c⟩ := hc
  exact ⟨c.comap (L2LocalMap f hf)⟩

end Se20Part
