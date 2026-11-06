import Se20Part.SpanningPatterns
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 1000000

/-- Edges at one fixed forward level; unlike `branchEdges`, this does not
include shorter levels. -/
def levelEdges {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ → V → V → Finset G.edgeSet
  | 0, u, v => if h : G.Adj u v then {⟨s(u,v),h⟩} else ∅
  | n+1, u, v => univ.biUnion (fun w : Forward G u v => levelEdges G n v w.val)

theorem levelEdges_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) (n : ℕ) {u v : V} (huv : G.Adj u v) :
    (levelEdges G n u v).card ≤ 3^n := by
  induction n generalizing u v with
  | zero => simp [levelEdges,huv]
  | succ n ih =>
    calc
      _ ≤ ∑ w : Forward G u v, (levelEdges G n v w.val).card := card_biUnion_le
      _ ≤ ∑ _w : Forward G u v, 3^n := sum_le_sum (fun w _ => ih w.property.1)
      _ ≤ 3 * 3^n := by
        simp only [sum_const,card_univ,nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (forward_card_le_three hd huv)
      _ = _ := by rw [pow_succ]; omega

theorem path_lastEdge_mem_level {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v y : V} (huv : G.Adj u v) (p : G.Walk v y) (hp : (Walk.cons huv p).IsPath) :
    (⟨s((Walk.cons huv p).penultimate,y),(Walk.cons huv p).adj_penultimate (by simp)⟩ : G.edgeSet)
      ∈ levelEdges G p.length u v := by
  induction p generalizing u with
  | @nil v => simp [levelEdges,huv]
  | @cons v w y hvw p ih =>
    have hh := (Walk.cons_isPath_iff huv (Walk.cons hvw p)).mp hp
    have hwu : w ≠ u := by
      intro heq
      apply hh.2
      simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr (heq ▸ p.start_mem_support)
    simp only [Walk.length_cons,levelEdges,mem_biUnion,mem_univ,true_and]
    refine ⟨⟨w,hvw,hwu⟩,?_⟩
    simpa only [Walk.penultimate_cons_cons] using ih hvw hh.1

def offPathNeighbors {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (Y : G.Walk u v) (i : ℕ) : Finset V :=
  (G.neighborFinset (Y.getVert i)).filter (fun x => x ∉ Y.support)

theorem offPathNeighbors_card_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {u v : V} (Y : G.Walk u v) (i : ℕ)
    {a : V} (ha : G.Adj (Y.getVert i) a) (hay : a ∈ Y.support) :
    (offPathNeighbors G Y i).card ≤ 3 := by
  have ha' : a ∉ offPathNeighbors G Y i := by simp [offPathNeighbors,hay]
  have hsub : insert a (offPathNeighbors G Y i) ⊆ G.neighborFinset (Y.getVert i) := by
    apply insert_subset
    · exact (G.mem_neighborFinset _ _).mpr ha
    · exact filter_subset _ _
  have hc := card_le_card hsub
  rw [card_insert_of_notMem ha',SimpleGraph.card_neighborFinset_eq_degree] at hc
  have := hd (Y.getVert i)
  omega

theorem offPathNeighbors_card_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {u v : V} (Y : G.Walk u v) (i : ℕ)
    {a b : V} (ha : G.Adj (Y.getVert i) a) (hb : G.Adj (Y.getVert i) b)
    (hay : a ∈ Y.support) (hby : b ∈ Y.support) (hne : a ≠ b) :
    (offPathNeighbors G Y i).card ≤ 2 := by
  have ha' : a ∉ offPathNeighbors G Y i := by simp [offPathNeighbors,hay]
  have hb' : b ∉ offPathNeighbors G Y i := by simp [offPathNeighbors,hby]
  have hsub : insert a (insert b (offPathNeighbors G Y i)) ⊆ G.neighborFinset (Y.getVert i) := by
    apply insert_subset
    · exact (G.mem_neighborFinset _ _).mpr ha
    apply insert_subset
    · exact (G.mem_neighborFinset _ _).mpr hb
    · exact filter_subset _ _
  have hc := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hne,ha']),card_insert_of_notMem hb',
    SimpleGraph.card_neighborFinset_eq_degree] at hc
  have := hd (Y.getVert i)
  omega

def projectedCandidates {V : Type*} (G : SimpleGraph V) {u v : V}
    (Y : G.Walk u v) (i d : ℕ) : Set G.edgeSet :=
  {r | ∃ P : EdgeProjection Y r, P.pos = i ∧ P.depth = d}

/-- A nearest-edge projection gives a simple branch of length d+1 whose last
edge is the candidate, and whose first edge leaves the path. -/
theorem projectedCandidates_mem_level {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} {Y : G.Walk u v} {i d : ℕ} (hd : 0 < d) {r : G.edgeSet}
    (hr : r ∈ projectedCandidates G Y i d) :
    ∃ w ∈ offPathNeighbors G Y i, r ∈ levelEdges G d (Y.getVert i) w := by
  obtain ⟨P,hpi,hpd⟩ := hr
  obtain ⟨z,hz⟩ := Sym2.mem_iff_exists.mp P.mem
  have hadj : G.Adj P.endpoint z := by simpa [hz] using r.property
  have hzmem : z ∈ r.val := by simp [hz]
  have hzout := P.other_endpoint_notMem hzmem hadj.ne.symm
  let p := Walk.cons hadj.symm P.stem
  have hpath : p.IsPath := P.stem_isPath.cons hzout
  let q := p.reverse
  have hq : q.IsPath := hpath.reverse
  have hlen : q.length = d+1 := by simp [q,p,P.length_stem,hpd]
  have hqn : ¬ q.Nil := by intro hn; have := Walk.Nil.length_eq_zero hn; omega
  have hroot : Y.getVert P.pos = Y.getVert i := congrArg Y.getVert hpi
  have hqfirst : G.Adj (Y.getVert P.pos) q.snd := q.adj_snd hqn
  have hoff : q.snd ∉ Y.support := by
    intro hsy
    have hmem : q.snd ∈ p.support := by simpa [q] using q.snd_mem_support
    rcases List.mem_cons.mp hmem with heq | hmem
    · have hzY : z ∈ Y.support := heq ▸ hsy
      obtain ⟨j,hj,hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hzY
      have hmin := P.minimal z hzmem j hjle ((Walk.nil : G.Walk z z).copy rfl hj.symm)
      simp only [Walk.length_copy,Walk.length_nil] at hmin
      omega
    · have heq := P.stem_intersection hmem hsy
      exact hqfirst.ne heq.symm
  have hlast : (⟨s(q.penultimate,z),q.adj_penultimate hqn⟩ : G.edgeSet) = r := by
    apply Subtype.ext
    change s(p.reverse.penultimate,z) = r.val
    rw [Walk.penultimate_reverse]
    simpa only [p,Walk.snd_cons] using hz.symm
  have hmem := path_lastEdge_mem_level hqfirst q.tail (by simpa only [Walk.cons_tail_eq q hqn] using hq)
  have htail : q.tail.length = d := by rw [Walk.length_tail,hlen]; omega
  simp only [Walk.cons_tail_eq q hqn,htail,hlast] at hmem
  refine ⟨q.snd,?_,?_⟩
  · exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr (by simpa [hpi] using hqfirst),hoff⟩
  · simpa only [hpi] using hmem

theorem projectedCandidates_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {u v : V} (Y : G.Walk u v) (i d : ℕ) (hdpos : 0 < d) :
    Nat.card (projectedCandidates G Y i d) ≤ (offPathNeighbors G Y i).card * 3^d := by
  have hsub : (projectedCandidates G Y i d).toFinset ⊆
      (offPathNeighbors G Y i).biUnion (fun w => levelEdges G d (Y.getVert i) w) := by
    intro r hr
    exact mem_biUnion.mpr (projectedCandidates_mem_level hdpos (Set.mem_toFinset.mp hr))
  have hc := (card_le_card hsub).trans card_biUnion_le
  have hb : (∑ w ∈ offPathNeighbors G Y i, (levelEdges G d (Y.getVert i) w).card) ≤
      (offPathNeighbors G Y i).card * 3^d := by
    calc
      _ ≤ ∑ _w ∈ offPathNeighbors G Y i, 3^d := by
        apply sum_le_sum
        intro w hw
        exact levelEdges_card hd d ((G.mem_neighborFinset _ _).mp (mem_filter.mp hw).1)
      _ = _ := by simp
  simpa only [Nat.card_eq_fintype_card,Set.toFinset_card] using hc.trans hb

def positionBranches (n i : ℕ) : ℕ := if i = 0 ∨ i = n then 3 else 2

theorem offPathNeighbors_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {u v : V} (Y : G.Walk u v) (hy : Y.IsPath)
    (hn : 0 < Y.length) (i : ℕ) (hi : i ≤ Y.length) :
    (offPathNeighbors G Y i).card ≤ positionBranches Y.length i := by
  by_cases hzero : i = 0
  · subst i
    simp only [positionBranches,true_or,ite_true]
    exact offPathNeighbors_card_le hd Y 0 (Y.adj_getVert_succ hn) (Y.getVert_mem_support 1)
  · have hipos : 0 < i := by omega
    have hprev : G.Adj (Y.getVert i) (Y.getVert (i-1)) := by
      have hh := (Y.adj_getVert_succ (show i-1 < Y.length by omega)).symm
      simpa only [Nat.sub_add_cancel hipos] using hh
    by_cases hend : i = Y.length
    · simp only [positionBranches,hend,or_true,ite_true]
      exact offPathNeighbors_card_le hd Y Y.length (by simpa [hend] using hprev) (Y.getVert_mem_support (i-1))
    · simp only [positionBranches,hzero,hend,false_or,ite_false]
      apply offPathNeighbors_card_le_two hd Y i hprev
        (Y.adj_getVert_succ (show i < Y.length by omega))
        (Y.getVert_mem_support (i-1)) (Y.getVert_mem_support (i+1))
      intro heq
      have hh := hy.getVert_injOn (by change i-1 ≤ Y.length; omega)
        (by change i+1 ≤ Y.length; omega) heq
      omega

theorem projectedCandidates_card_explicit {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {u v : V} (Y : G.Walk u v) (hy : Y.IsPath)
    (hn : 0 < Y.length) (i d : ℕ) (hi : i ≤ Y.length) (hdpos : 0 < d) :
    Nat.card (projectedCandidates G Y i d) ≤ positionBranches Y.length i * 3^d :=
  (projectedCandidates_card hd Y i d hdpos).trans
    (Nat.mul_le_mul_right _ (offPathNeighbors_card hd Y hy hn i hi))

end Se20Part
