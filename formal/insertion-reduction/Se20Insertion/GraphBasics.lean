import Se20Insertion.Definitions

noncomputable section
open scoped Classical
namespace Se20Insertion
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- An injective graph homomorphism preserves ambient conflicts. -/
def L2Map (f : G →g H) (hinj : Function.Injective f) : L2 G →g L2 H where
  toFun := f.mapEdgeSet
  map_rel' := by
    rintro e g ⟨hne, x, hx, y, hy, hxy⟩
    refine ⟨?_, f x, ?_, f y, ?_, ?_⟩
    · intro heq
      apply hne
      apply Subtype.ext
      exact Sym2.map.injective hinj (congrArg Subtype.val heq)
    · exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
    · exact Sym2.mem_map.mpr ⟨y, hy, rfl⟩
    · exact hxy.elim (fun h => Or.inl (congrArg f h)) (fun h => Or.inr (f.map_adj h))

/-- In an induced subgraph the converse also holds: a joining edge has both
endpoints in the retained vertices. This includes deletion of a vertex. -/
theorem L2_embedding_adj_iff (f : G ↪g H) (e g : G.edgeSet) :
    (L2 H).Adj (f.mapEdgeSet e) (f.mapEdgeSet g) ↔ (L2 G).Adj e g := by
  constructor
  · rintro ⟨hne, x', hx', y', hy', hxy⟩
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hx'
    obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hy'
    refine ⟨fun h => hne (congrArg f.mapEdgeSet h), x, hx, y, hy, ?_⟩
    exact hxy.elim (fun h => Or.inl (f.injective h)) (fun h => Or.inr (f.map_adj_iff.mp h))
  · exact (L2Map f.toHom f.injective).map_adj

def inducedEmbedding (G : SimpleGraph V) (S : Set V) : G.induce S ↪g G where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

theorem L2_induce_adj_iff (G : SimpleGraph V) (S : Set V)
    (e f : (G.induce S).edgeSet) :
    (L2 G).Adj ((inducedEmbedding G S).mapEdgeSet e)
      ((inducedEmbedding G S).mapEdgeSet f) ↔ (L2 (G.induce S)).Adj e f :=
  L2_embedding_adj_iff (inducedEmbedding G S) e f

theorem L2_deleteVertex_adj_iff (G : SimpleGraph V) (v : V)
    (e f : (G.induce {x | x ≠ v}).edgeSet) :
    (L2 G).Adj ((inducedEmbedding G {x | x ≠ v}).mapEdgeSet e)
      ((inducedEmbedding G {x | x ≠ v}).mapEdgeSet f) ↔
        (L2 (G.induce {x | x ≠ v})).Adj e f :=
  L2_induce_adj_iff G _ e f

theorem strongColourable_mono {G H : SimpleGraph V} (hGH : G ≤ H) {k : ℕ}
    (h : StrongColourable H k) : StrongColourable G k := by
  obtain ⟨c⟩ := h
  exact ⟨c.comap (L2Map (SimpleGraph.Hom.ofLE hGH) Function.injective_id)⟩

theorem strongColourable_of_iso (f : G ≃g H) {k : ℕ}
    (h : StrongColourable H k) : StrongColourable G k := by
  obtain ⟨c⟩ := h
  exact ⟨c.comap (L2Map f.toHom f.injective)⟩

/-- Transfer a theorem quantified over `Fin n` to any finite vertex type. -/
theorem strongColourable_of_fin
    (hfin : ∀ n (G : SimpleGraph (Fin n)), MaxDegreeFour G → StrongColourable G 20)
    [Fintype V] (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) :
    StrongColourable G 20 := by
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let i : H ≃g G := SimpleGraph.Iso.comap e G
  have hH : MaxDegreeFour H := by
    intro v
    have hd := Nat.card_congr (i.mapNeighborSet v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at *
    exact hd.le.trans (hΔ (i v))
  exact strongColourable_of_iso i.symm (hfin _ H hH)

end Se20Insertion
