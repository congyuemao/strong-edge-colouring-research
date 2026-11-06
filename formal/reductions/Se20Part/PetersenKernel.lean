import Se20Part.ListBlockExtension

namespace Se20Part

/-- The ten two-subsets of a five-element set, in lexicographic order. -/
def petersenVertex : Fin 10 → Finset (Fin 5) :=
  ![{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}]

def PetersenGraph : SimpleGraph (Fin 10) where
  Adj u v := u ≠ v ∧ Disjoint (petersenVertex u) (petersenVertex v)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel PetersenGraph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ Disjoint _ _))

/-- Edges are indexed by the missing element and a two-two partition. -/
def petersenEnds (v : Fin 5 × Fin 3) : Fin 10 × Fin 10 :=
  (![![(4,9),(5,8),(6,7)], ![(1,9),(2,8),(3,7)],
    ![(0,9),(2,6),(3,5)], ![(0,8),(1,6),(3,4)], ![(0,7),(1,5),(2,4)]] v.1) v.2

theorem petersenEnds_adj : ∀ v, PetersenGraph.Adj (petersenEnds v).1 (petersenEnds v).2 := by
  decide +kernel

def petersenEdge (v : Fin 5 × Fin 3) : PetersenGraph.edgeSet :=
  ⟨s((petersenEnds v).1,(petersenEnds v).2), PetersenGraph.mem_edgeSet.mpr (petersenEnds_adj v)⟩

theorem petersenEdge_injective : Function.Injective petersenEdge := by decide +kernel

theorem petersen_fifteen_edges : Fintype.card PetersenGraph.edgeSet = 15 := by
  rw [SimpleGraph.card_edgeSet]
  decide +kernel

theorem petersen_cubic : ∀ v, PetersenGraph.degree v = 3 := by decide +kernel

instance : DecidableRel (L2 PetersenGraph).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ ∃ a ∈ _, ∃ b ∈ _, a = b ∨ PetersenGraph.Adj a b))

set_option maxRecDepth 10000 in
theorem petersenEdge_conflict : ∀ u v,
    (L2 PetersenGraph).Adj (petersenEdge u) (petersenEdge v) ↔ u.1 ≠ v.1 := by
  decide +kernel

/-- A kernel-checked identification of the actual edge-conflict graph. -/
noncomputable def petersenConflictIso : ThreePartGraph (Fin 5) ≃g L2 PetersenGraph where
  toEquiv := Equiv.ofBijective petersenEdge
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨petersenEdge_injective,by rw [petersen_fifteen_edges]; decide⟩)
  map_rel_iff' := petersenEdge_conflict _ _

theorem petersen_eight_choosable {C : Type*} [DecidableEq C]
    (L : PetersenGraph.edgeSet → Finset C) (hL : ∀ v, 8 ≤ (L v).card) :
    HasListColouring (L2 PetersenGraph) L := by
  obtain ⟨c,hc,hp⟩ := five_parts_eight_choosable (by simp)
    (fun v => L (petersenConflictIso v)) (fun v => hL _)
  refine ⟨fun e => c (petersenConflictIso.symm e),?_,?_⟩
  · intro e; simpa using hc (petersenConflictIso.symm e)
  · intro e f hef; exact hp _ _ (petersenConflictIso.symm.toHom.map_adj hef)

end Se20Part
