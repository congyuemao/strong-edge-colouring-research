import Se20Part.SpanningGeometry
import Mathlib.Data.Nat.Dist

noncomputable section
open scoped Classical
open SimpleGraph
namespace Se20Part

def forwardSegment {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    {i j : ℕ} (hij : i ≤ j) : G.Walk (Y.getVert i) (Y.getVert j) :=
  ((Y.drop i).take (j-i)).copy rfl (by simp [Nat.add_sub_of_le hij])

theorem forwardSegment_length {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Y.length) :
    (forwardSegment Y hij).length = j-i := by
  simp [forwardSegment,Nat.min_eq_left (show j-i ≤ Y.length-i by omega)]

theorem forwardSegment_isPath {V : Type*} {G : SimpleGraph V} {u v : V} {Y : G.Walk u v}
    (hy : Y.IsPath) {i j : ℕ} (hij : i ≤ j) : (forwardSegment Y hij).IsPath := by
  simpa [forwardSegment] using (hy.drop i).take (j-i)

theorem forwardSegment_support {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    {i j : ℕ} (hij : i ≤ j) : (forwardSegment Y hij).support ⊆ Y.support := by
  simp only [forwardSegment,Walk.support_copy,Walk.support_take,Walk.drop_support_eq_support_drop_min]
  intro x hx
  exact List.drop_subset _ _ (List.take_subset _ _ hx)

theorem forwardSegment_vertex {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    {i j k : ℕ} (hij : i ≤ j) (hik : i ≤ k) (hkj : k ≤ j) :
    Y.getVert k ∈ (forwardSegment Y hij).support := by
  have hh := (forwardSegment Y hij).getVert_mem_support (k-i)
  simpa [forwardSegment,Nat.min_eq_right (show k-i ≤ j-i by omega),Nat.add_sub_of_le hik] using hh

def pathSegment {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    (i j : ℕ) : G.Walk (Y.getVert i) (Y.getVert j) :=
  if h : i ≤ j then forwardSegment Y h else (forwardSegment Y (Nat.le_of_not_ge h)).reverse

theorem pathSegment_length {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    {i j : ℕ} (hi : i ≤ Y.length) (hj : j ≤ Y.length) :
    (pathSegment Y i j).length = Nat.dist i j := by
  unfold pathSegment
  split_ifs with h
  · rw [forwardSegment_length _ h hj,Nat.dist_eq_sub_of_le h]
  · rw [Walk.length_reverse,forwardSegment_length _ _ hi,Nat.dist_eq_sub_of_le_right (by omega)]

theorem pathSegment_isPath {V : Type*} {G : SimpleGraph V} {u v : V} {Y : G.Walk u v}
    (hy : Y.IsPath) (i j : ℕ) : (pathSegment Y i j).IsPath := by
  unfold pathSegment
  split_ifs
  · exact forwardSegment_isPath hy _
  · exact (forwardSegment_isPath hy _).reverse

theorem pathSegment_support {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    (i j : ℕ) : (pathSegment Y i j).support ⊆ Y.support := by
  unfold pathSegment
  split_ifs
  · exact forwardSegment_support _ _
  · simpa using forwardSegment_support Y _

theorem pathSegment_vertex {V : Type*} {G : SimpleGraph V} {u v : V} (Y : G.Walk u v)
    {i j k : ℕ} (hk : min i j ≤ k ∧ k ≤ max i j) :
    Y.getVert k ∈ (pathSegment Y i j).support := by
  unfold pathSegment
  split_ifs with h
  · exact forwardSegment_vertex Y h (by simpa [min_eq_left h] using hk.1)
      (by simpa [max_eq_right h] using hk.2)
  · simp only [Walk.support_reverse,List.mem_reverse]
    exact forwardSegment_vertex Y _ (by simpa [min_eq_right (by omega : j ≤ i)] using hk.1)
      (by simpa [max_eq_left (by omega : j ≤ i)] using hk.2)

theorem path_append_of_intersection {V : Type*} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} {q : G.Walk v w} (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ x ∈ p.support, x ∈ q.support → x = v) : (p.append q).IsPath := by
  induction p with
  | nil => simpa using hq
  | @cons a b c h p ih =>
    have hh : p.IsPath ∧ a ∉ p.support := by simpa using hp
    apply Walk.IsPath.cons
    · apply ih hh.1 hq
      intro x hx hxq
      exact hi x (by simp [hx]) hxq
    · intro ha
      have ha' : a ∈ p.support ∨ a ∈ q.support := by
        simpa only [Walk.mem_support_append_iff] using ha
      rcases ha' with ha' | ha'
      · exact hh.2 ha'
      · have heq := hi a (by simp) ha'
        exact hh.2 (heq ▸ p.end_mem_support)

/-- The closest endpoint and closest vertex of Y, using walk lengths so disconnected
graphs cannot create spurious distance-zero minimizers. -/
structure EdgeProjection {V : Type*} {G : SimpleGraph V} {u v : V}
    (Y : G.Walk u v) (r : G.edgeSet) where
  pos : ℕ
  pos_le : pos ≤ Y.length
  depth : ℕ
  endpoint : V
  mem : endpoint ∈ r.val
  stem : G.Walk endpoint (Y.getVert pos)
  length_stem : stem.length = depth
  minimal : ∀ x ∈ r.val, ∀ i ≤ Y.length, ∀ q : G.Walk x (Y.getVert i), depth ≤ q.length

theorem edgeProjection_exists {V : Type*} {G : SimpleGraph V} {u v : V}
    (Y : G.Walk u v) (r : G.edgeSet)
    (h : ∃ i ≤ Y.length, ∃ x ∈ r.val, Nonempty (G.Walk x (Y.getVert i))) :
    Nonempty (EdgeProjection Y r) := by
  have hex : ∃ n, ∃ i ≤ Y.length, ∃ x ∈ r.val, ∃ q : G.Walk x (Y.getVert i), q.length = n := by
    obtain ⟨i,hi,x,hx,⟨q⟩⟩ := h
    exact ⟨q.length,i,hi,x,hx,q,rfl⟩
  obtain ⟨i,hi,x,hx,q,hq⟩ := Nat.find_spec hex
  exact ⟨⟨i,hi,Nat.find hex,x,hx,q,hq,fun x hx j hj p =>
    Nat.find_min' hex ⟨j,hj,x,hx,p,rfl⟩⟩⟩

theorem EdgeProjection.stem_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    {Y : G.Walk u v} {r : G.edgeSet} (P : EdgeProjection Y r) : P.stem.IsPath := by
  apply P.stem.isPath_of_length_eq_dist
  apply le_antisymm
  · obtain ⟨q,_,hq⟩ := P.stem.reachable.exists_path_of_dist
    rw [P.length_stem,← hq]
    exact P.minimal _ P.mem _ P.pos_le q
  · exact G.dist_le P.stem

theorem EdgeProjection.stem_intersection {V : Type*} {G : SimpleGraph V} {u v : V}
    {Y : G.Walk u v} {r : G.edgeSet} (P : EdgeProjection Y r)
    {x : V} (hx : x ∈ P.stem.support) (hy : x ∈ Y.support) : x = Y.getVert P.pos := by
  obtain ⟨i,hi,hile⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  by_contra hne
  have hlt := P.stem.length_takeUntil_lt_length hx hne
  have hmin := P.minimal P.endpoint P.mem i hile ((P.stem.takeUntil x hx).copy rfl hi.symm)
  simp only [Walk.length_copy] at hmin
  rw [P.length_stem] at hlt
  omega

theorem EdgeProjection.other_endpoint_notMem {V : Type*} {G : SimpleGraph V} {u v : V}
    {Y : G.Walk u v} {r : G.edgeSet} (P : EdgeProjection Y r)
    {x : V} (hx : x ∈ r.val) (hne : x ≠ P.endpoint) : x ∉ P.stem.support := by
  intro hh
  have hlt := P.stem.length_dropUntil_lt_length hh hne
  have hmin := P.minimal x hx P.pos P.pos_le (P.stem.dropUntil x hh)
  rw [P.length_stem] at hlt
  omega

theorem EdgeProjection.route {V : Type*} {G : SimpleGraph V} {u v : V}
    {Y : G.Walk u v} {r : G.edgeSet} (P : EdgeProjection Y r)
    (havoid : ∀ x ∈ r.val, x ∉ Y.support) {x : V} (hx : x ∈ r.val) :
    ∃ s : G.Walk x (Y.getVert P.pos), s.IsPath ∧ P.depth ≤ s.length ∧
      s.length ≤ P.depth+1 ∧ ∀ z ∈ s.support, z ∈ Y.support → z = Y.getVert P.pos := by
  by_cases heq : x = P.endpoint
  · subst x
    exact ⟨P.stem,P.stem_isPath,by rw [P.length_stem],by rw [P.length_stem]; omega,
      fun _ hz hy => P.stem_intersection hz hy⟩
  · have he : r.val = s(x,P.endpoint) := (Sym2.mem_and_mem_iff heq).mp ⟨hx,P.mem⟩
    have hadj : G.Adj x P.endpoint := by simpa [he] using r.property
    refine ⟨.cons hadj P.stem,P.stem_isPath.cons (P.other_endpoint_notMem hx heq),?_,?_,?_⟩
    · simp [P.length_stem]
    · simp [P.length_stem]
    · intro z hz hy
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (havoid z hx hy).elim
      · exact P.stem_intersection hz hy

/-- Gate property for all paths of length at most seven to Y. This supplies both
the depth/position length bound and the whole interval between the two positions. -/
theorem EdgeProjection.short_gate {V : Type*} {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : GirthAtLeast G g) (h42 : 42 ≤ g) {Y : G.Walk u v}
    (hy : Y.IsPath) (hlen : 2*Y.length < g) {r : G.edgeSet}
    (P : EdgeProjection Y r) (hdepth : P.depth ≤ 6)
    (havoid : ∀ x ∈ r.val, x ∉ Y.support) {x : V} (hx : x ∈ r.val)
    {j : ℕ} (hj : j ≤ Y.length) (q : G.Walk x (Y.getVert j))
    (hq : q.IsPath) (hql : q.length ≤ 7) :
    P.depth + Nat.dist P.pos j ≤ q.length ∧
      ∀ k, min P.pos j ≤ k → k ≤ max P.pos j → Y.getVert k ∈ q.support := by
  obtain ⟨s,hs,hslo,hshi,hsint⟩ := P.route havoid hx
  let t := pathSegment Y P.pos j
  have ht : t.IsPath := pathSegment_isPath hy _ _
  have htlen : t.length = Nat.dist P.pos j := pathSegment_length Y P.pos_le hj
  have hdist : Nat.dist P.pos j ≤ Y.length := by unfold Nat.dist; have := P.pos_le; omega
  have hst : (s.append t).IsPath := by
    apply path_append_of_intersection hs ht
    intro z hz hzt
    exact hsint z hz (pathSegment_support Y _ _ hzt)
  have heq : s.append t = q := short_paths_unique hg hst hq (by
    simp only [Walk.length_append,htlen]
    omega)
  constructor
  · have hh := congrArg Walk.length heq
    simp only [Walk.length_append,htlen] at hh
    omega
  · intro k hk hk'
    rw [← heq,Walk.mem_support_append_iff]
    exact Or.inr (pathSegment_vertex Y ⟨hk,hk'⟩)

theorem EdgeProjection.depth_pos_unique {V : Type*} {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : GirthAtLeast G g) (h42 : 42 ≤ g) {Y : G.Walk u v}
    (hy : Y.IsPath) (hlen : 2*Y.length < g) {r : G.edgeSet}
    (P Q : EdgeProjection Y r) (hdepth : P.depth ≤ 6)
    (havoid : ∀ x ∈ r.val, x ∉ Y.support) : P.depth = Q.depth ∧ P.pos = Q.pos := by
  have hd : P.depth = Q.depth := le_antisymm
    (by simpa [Q.length_stem] using P.minimal _ Q.mem _ Q.pos_le Q.stem)
    (by simpa [P.length_stem] using Q.minimal _ P.mem _ P.pos_le P.stem)
  refine ⟨hd,?_⟩
  have hgate := (P.short_gate hg h42 hy hlen hdepth havoid Q.mem Q.pos_le Q.stem
    Q.stem_isPath (by rw [Q.length_stem,← hd]; omega)).1
  rw [Q.length_stem,← hd] at hgate
  unfold Nat.dist at hgate
  omega

theorem EdgeProjection.positive {V : Type*} {G : SimpleGraph V} {u v : V}
    {Y : G.Walk u v} {r : G.edgeSet} (P : EdgeProjection Y r)
    (havoid : ∀ x ∈ r.val, x ∉ Y.support) : 1 ≤ P.depth := by
  by_contra! hn
  have hs : P.stem.Nil := Walk.length_eq_zero_iff.mp (by rw [P.length_stem]; omega)
  have heq : P.endpoint = Y.getVert P.pos := hs.eq
  exact havoid P.endpoint P.mem (heq ▸ Y.getVert_mem_support P.pos)

theorem EdgeProjection.metric_minimal {V : Type*} {G : SimpleGraph V} {u v : V}
    {Y : G.Walk u v} {r : G.edgeSet} (P : EdgeProjection Y r) :
    (∀ x ∈ r.val, ∀ i ≤ Y.length, (P.depth : ℕ∞) ≤ G.edist x (Y.getVert i)) ∧
      G.edist P.endpoint (Y.getVert P.pos) = P.depth := by
  have hl : ∀ x ∈ r.val, ∀ i ≤ Y.length, (P.depth : ℕ∞) ≤ G.edist x (Y.getVert i) := by
    intro x hx i hi
    by_cases ht : G.edist x (Y.getVert i) = ⊤
    · simp [ht]
    · obtain ⟨q,hq⟩ := G.exists_walk_of_edist_ne_top ht
      rw [← hq]
      exact_mod_cast P.minimal x hx i hi q
  refine ⟨hl,le_antisymm ?_ (hl _ P.mem _ P.pos_le)⟩
  simpa [P.length_stem] using P.stem.edist_le

theorem walk_split_edge {V : Type*} {G : SimpleGraph V} {u v a b : V}
    (p : G.Walk u v) (he : s(a,b) ∈ p.edges) :
    (∃ l : G.Walk u a, ∃ t : G.Walk b v, ∃ h : G.Adj a b, p = l.append (.cons h t)) ∨
    (∃ l : G.Walk u b, ∃ t : G.Walk a v, ∃ h : G.Adj b a, p = l.append (.cons h t)) := by
  induction p with
  | nil => simp at he
  | @cons x y z h p ih =>
    rcases List.mem_cons.mp he with hh | hh
    · rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨.nil,p,h,rfl⟩
      · exact Or.inr ⟨.nil,p,h,rfl⟩
    · rcases ih hh with ⟨l,t,ha,hp⟩ | ⟨l,t,ha,hp⟩
      · exact Or.inl ⟨.cons h l,t,ha,by simp [hp]⟩
      · exact Or.inr ⟨.cons h l,t,ha,by simp [hp]⟩

theorem projections_span_oriented_edge {V : Type*} {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : GirthAtLeast G g) (h42 : 42 ≤ g) {Y : G.Walk u v}
    (hy : Y.IsPath) (hlen : 2*Y.length < g) {r r' : G.edgeSet}
    (P : EdgeProjection Y r) (Q : EdgeProjection Y r')
    (hav : ∀ x ∈ r.val, x ∉ Y.support) (hav' : ∀ x ∈ r'.val, x ∉ Y.support)
    {j : ℕ} (hj : j < Y.length) {x y : V} (hx : x ∈ r.val) (hy' : y ∈ r'.val)
    (l : G.Walk x (Y.getVert j)) (t : G.Walk (Y.getVert (j+1)) y)
    (h : G.Adj (Y.getVert j) (Y.getVert (j+1)))
    (hp : (l.append (.cons h t)).IsPath) (hpl : l.length+1+t.length ≤ 7) :
    P.pos ≤ j ∧ j < Q.pos ∧ P.depth + Q.depth + (Q.pos-P.pos) ≤ 7 := by
  have hlp := hp.of_append_left
  have htp := hp.of_append_right.of_cons
  have hl : l.length ≤ 6 := by omega
  have ht : t.length ≤ 6 := by omega
  have hP : P.depth ≤ 6 := (P.minimal _ hx j (by omega) l).trans hl
  have hQ : Q.depth ≤ 6 := (Q.minimal _ hy' (j+1) (by omega) t.reverse).trans (by simpa using ht)
  have gateP := P.short_gate hg h42 hy hlen hP hav hx (by omega) l hlp (by omega)
  have gateQ := Q.short_gate hg h42 hy hlen hQ hav' hy' (by omega) t.reverse htp.reverse
    (by simpa using (show t.length ≤ 7 by omega))
  have hdis : l.support.Disjoint t.support := by
    have hh := (Walk.isPath_append l (.cons h t)).mp hp
    simpa using hh.2.2
  have hpos : P.pos ≤ j := by
    by_contra! hn
    have hh := gateP.2 (j+1) (by omega) (by omega)
    exact List.disjoint_left.mp hdis hh t.start_mem_support
  have hpos' : j < Q.pos := by
    by_contra! hn
    have hh := gateQ.2 j (by omega) (by omega)
    have hnot : Y.getVert j ∉ t.support := by simpa using (Walk.cons_isPath_iff h t).mp hp.of_append_right |>.2
    exact hnot (by simpa using hh)
  refine ⟨hpos,hpos',?_⟩
  have hlbound := gateP.1
  have htbound := gateQ.1
  rw [Nat.dist_eq_sub_of_le hpos] at hlbound
  rw [Nat.dist_eq_sub_of_le_right (by omega),Walk.length_reverse] at htbound
  omega

theorem bridge_spans {V : Type*} {G : SimpleGraph V} {u v : V} {g : ℕ}
    (hg : GirthAtLeast G g) (h42 : 42 ≤ g) {Y : G.Walk u v}
    (hy : Y.IsPath) (hlen : 2*Y.length < g) {D : Set G.edgeSet}
    (hav : ∀ r ∈ D, ∀ x ∈ r.val, x ∉ Y.support)
    {j : ℕ} (hj : j < Y.length) (hb : DefectBridge G D s(Y.getVert j,Y.getVert (j+1))) :
    ∃ r ∈ D, ∃ r' ∈ D, r ≠ r' ∧
      ∃ P : EdgeProjection Y r, ∃ Q : EdgeProjection Y r',
        P.depth ≤ 5 ∧ Q.depth ≤ 5 ∧ P.pos ≤ j ∧ j < Q.pos ∧
          P.depth+Q.depth+(Q.pos-P.pos) ≤ 7 := by
  obtain ⟨r,hr,r',hr',hne,x,hx,y,hy',p,hp,hpl,he⟩ := hb
  have oriented {r r' : G.edgeSet} (hr : r ∈ D) (hr' : r' ∈ D) (hne : r ≠ r')
      {x y : V} (hx : x ∈ r.val) (hy' : y ∈ r'.val)
      (l : G.Walk x (Y.getVert j)) (t : G.Walk (Y.getVert (j+1)) y)
      (h : G.Adj (Y.getVert j) (Y.getVert (j+1)))
      (hp : (l.append (.cons h t)).IsPath) (hpl : l.length+1+t.length ≤ 7) :
      ∃ P : EdgeProjection Y r, ∃ Q : EdgeProjection Y r',
        P.depth ≤ 5 ∧ Q.depth ≤ 5 ∧ P.pos ≤ j ∧ j < Q.pos ∧
          P.depth+Q.depth+(Q.pos-P.pos) ≤ 7 := by
    obtain ⟨P⟩ := edgeProjection_exists Y r ⟨j,by omega,x,hx,⟨l⟩⟩
    obtain ⟨Q⟩ := edgeProjection_exists Y r' ⟨j+1,by omega,y,hy',⟨t.reverse⟩⟩
    obtain ⟨hpos,hpos',hb⟩ := projections_span_oriented_edge hg h42 hy hlen P Q
      (hav r hr) (hav r' hr') hj hx hy' l t h hp hpl
    have hP := P.positive (hav r hr)
    have hQ := Q.positive (hav r' hr')
    exact ⟨P,Q,by omega,by omega,hpos,hpos',hb⟩
  rcases walk_split_edge p he with ⟨l,t,h,rfl⟩ | ⟨l,t,h,rfl⟩
  · exact ⟨r,hr,r',hr',hne,oriented hr hr' hne hx hy' l t h hp (by
      simp only [Walk.length_append,Walk.length_cons] at hpl
      omega)⟩
  · have hp' : (t.reverse.append (.cons h.symm l.reverse)).IsPath := by
      have hh := hp.reverse
      simp only [Walk.reverse_append,Walk.reverse_cons,Walk.concat_eq_append] at hh
      simpa only [← Walk.append_assoc,Walk.cons_append,Walk.nil_append] using hh
    exact ⟨r',hr',r,hr,Ne.symm hne,oriented hr' hr (Ne.symm hne) hy' hx
      t.reverse l.reverse h.symm hp' (by
        simp only [Walk.length_append,Walk.length_cons] at hpl
        simp only [Walk.length_reverse]
        omega)⟩

end Se20Part
