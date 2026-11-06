import Se20Part.TransferAutomaton
import Se20Part.SpanningFamily

noncomputable section
open scoped Classical BigOperators
open SimpleGraph
namespace Se20Part
set_option maxHeartbeats 1000000

def SpanningFamily.depthPattern {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y) (j : ℕ) : ℕ :=
  if h : ∃ r : F.edges, (F.projection r).pos = j then (F.projection h.choose).depth else 0

theorem SpanningFamily.depthPattern_at {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y)
    (hinj : Function.Injective (fun r => (F.projection r).pos)) (r : F.edges) :
    F.depthPattern (F.projection r).pos = (F.projection r).depth := by
  have hex : ∃ r' : F.edges, (F.projection r').pos = (F.projection r).pos := ⟨r,rfl⟩
  rw [depthPattern,dif_pos hex]
  have heq : hex.choose = r := hinj hex.choose_spec
  rw [heq]

theorem SpanningFamily.depthPattern_positive {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y)
    {j : ℕ} (hj : 0 < F.depthPattern j) :
    ∃ r : F.edges, (F.projection r).pos = j ∧ (F.projection r).depth = F.depthPattern j := by
  unfold depthPattern at hj ⊢
  split_ifs at hj ⊢ with hex
  · exact ⟨hex.choose,hex.choose_spec,rfl⟩
  · omega

theorem SpanningFamily.depthPattern_bounded {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y) (j : ℕ) :
    F.depthPattern j ≤ 5 := by
  unfold depthPattern
  split_ifs with h
  · exact F.depth_le h.choose
  · omega

/-- The geometric separation and spanning assertions imply the exact scalar
conditions checked by the transition automaton, for all path lengths. -/
theorem SpanningFamily.validDepthPattern {V : Type*} {G : SimpleGraph V} {u v : V}
    {D : Set G.edgeSet} {Y : G.Walk u v} (F : SpanningFamily D Y)
    (hinj : Function.Injective (fun r => (F.projection r).pos))
    (hs : Separated G 5 D) (hlen : 0 < Y.length) :
    ValidDepthPattern F.depthPattern Y.length := by
  refine ⟨?_,fun j _ => F.depthPattern_bounded j,?_,?_⟩
  · obtain ⟨r,r',hr,hr',hb⟩ := F.spans 0 hlen
    have hp : (F.projection r).pos = 0 := by omega
    have heq := F.depthPattern_at hinj r
    rw [hp] at heq
    have := F.positive r
    omega
  · intro i j hij hj hfi hfj
    obtain ⟨r,hri,hrd⟩ := F.depthPattern_positive hfi
    obtain ⟨r',hrj,hrd'⟩ := F.depthPattern_positive hfj
    have hne : r ≠ r' := by intro heq; subst r'; omega
    have hh := F.pair_spacing hs r r' hne
    rw [hri,hrj,hrd,hrd',Nat.dist_eq_sub_of_le (by omega : i ≤ j)] at hh
    exact hh
  · intro j hj
    obtain ⟨r,r',hl,hr,hb⟩ := F.spans j hj
    refine ⟨(F.projection r).pos,(F.projection r').pos,hl,hr,(F.projection r').pos_le,?_,?_,?_⟩
    · rw [F.depthPattern_at hinj r]; exact F.positive r
    · rw [F.depthPattern_at hinj r']; exact F.positive r'
    · simpa only [F.depthPattern_at hinj r,F.depthPattern_at hinj r'] using hb

end Se20Part
