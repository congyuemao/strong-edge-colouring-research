import Se20Insertion.DegreeListBrooks

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.FiniteConnectivity
variable {W : Type*} [DecidableEq W] (H : SimpleGraph W)

/-- Ambient walks with an explicit forbidden vertex set. -/
def Avoids (S : Finset W) (x y : W) : Prop :=
  ∃ p : H.Walk x y, ∀ z ∈ p.support, z ∉ S

theorem Avoids.left {S : Finset W} {x y : W} (h : Avoids H S x y) : x ∉ S :=
  h.choose_spec x h.choose.start_mem_support

theorem Avoids.right {S : Finset W} {x y : W} (h : Avoids H S x y) : y ∉ S :=
  h.choose_spec y h.choose.end_mem_support

theorem Avoids.refl {S : Finset W} {x : W} (hx : x ∉ S) : Avoids H S x x :=
  ⟨.nil,by simpa using hx⟩

theorem Avoids.adj {S : Finset W} {x y : W} (hxy : H.Adj x y)
    (hx : x ∉ S) (hy : y ∉ S) : Avoids H S x y :=
  ⟨.cons hxy .nil,by simpa using And.intro hx hy⟩

theorem Avoids.symm {S : Finset W} {x y : W} (h : Avoids H S x y) : Avoids H S y x := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

theorem Avoids.trans {S : Finset W} {x y z : W} (h : Avoids H S x y) (h' : Avoids H S y z) :
    Avoids H S x z := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := h'
  exact ⟨p.append q,fun w hw => ((SimpleGraph.Walk.mem_support_append_iff _ _).mp hw).elim
    (hp w) (hq w)⟩

theorem Avoids.exists_path {S : Finset W} {x y : W} (h : Avoids H S x y) :
    ∃ p : H.Walk x y, p.IsPath ∧ ∀ z ∈ p.support, z ∉ S := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.toPath, p.toPath.prop, fun z hz => hp z (p.support_toPath_subset_support hz)⟩

theorem avoids_of_delete_connected {v x y : W} (hc : (H.induce {z | z ≠ v}).Connected)
    (hx : x ≠ v) (hy : y ≠ v) : Avoids H {v} x y := by
  obtain ⟨p⟩ := hc ⟨x,hx⟩ ⟨y,hy⟩
  refine ⟨p.map (SimpleGraph.Embedding.induce (G := H) {z | z ≠ v}).toHom,?_⟩
  intro z hz
  change z ∈ (p.map (SimpleGraph.Embedding.induce (G := H) {z | z ≠ v}).toHom).support at hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
  change w.val ∉ ({v} : Finset W)
  simpa only [Finset.mem_singleton, Set.mem_ofPred_eq] using w.prop

theorem connected_delete_of_root (S : Finset W) (r : W) (hr : r ∉ S)
    (hall : ∀ x, x ∉ S → Avoids H S r x) : (H.induce {x | x ∉ S}).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨r,hr⟩⟩ }
  intro x y
  obtain ⟨p,hp⟩ := Avoids.trans H (Avoids.symm H (hall x.val x.prop)) (hall y.val y.prop)
  exact ⟨p.induce {x | x ∉ S} hp⟩

theorem suffix_avoids_start {x y z : W} {p : H.Walk x y} (hp : p.IsPath)
    (hz : z ∈ p.support) (hzx : z ≠ x) : x ∉ (p.dropUntil z hz).support := by
  cases p with
  | nil => exact (hzx (by simpa using hz)).elim
  | @cons x a y hxa q =>
    have hn : x ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hzq : z ∈ q.support := (List.mem_cons.mp hz).resolve_left hzx
    simpa only [SimpleGraph.Walk.dropUntil,dite_eq_right hzx.symm] using
      (fun hh => hn (q.support_dropUntil_subset_support hzq hh) : x ∉ (q.dropUntil z hzq).support)

/-- A vertex separating r from z lies strictly earlier on a shortest path;
its suffix connects the separator to z without revisiting r. -/
theorem separator_distance (hc : H.Connected) {r u z : W} (hur : u ≠ r) (huz : u ≠ z)
    (hn : ¬ Avoids H {u} r z) : H.dist r u < H.dist r z ∧ Avoids H {r} u z := by
  obtain ⟨p,hp,hplen⟩ := hc.exists_path_of_dist r z
  have hu : u ∈ p.support := by
    by_contra hu
    apply hn
    exact ⟨p,fun x hx => by simp only [Finset.mem_singleton]; intro he; exact hu (he ▸ hx)⟩
  refine ⟨?_,p.dropUntil u hu,?_⟩
  · have h1 := SimpleGraph.dist_le (p.takeUntil u hu)
    have h2 := SimpleGraph.Walk.length_takeUntil_lt_length hu huz
    omega
  · intro x hx
    simp only [Finset.mem_singleton]
    intro he
    exact suffix_avoids_start H hp hu hur (he ▸ hx)

/-- Every component left after deleting one vertex contains a marked vertex. -/
def Attached (N : W → Prop) : Prop :=
  ∀ u x, x ≠ u → ∃ z, N z ∧ Avoids H {u} x z

variable [Fintype W]

/-- Choose a marked vertex farthest from r inside a branch of H-r.
It cannot be a cut vertex: a component beyond it would contain a farther
marked vertex in the same branch. -/
theorem farthest_marked_noncut (hc : H.Connected) (N : W → Prop) (ha : Attached H N)
    {r x : W} (hxr : x ≠ r) :
    ∃ u, N u ∧ Avoids H {r} x u ∧ (H.induce {z | z ≠ u}).Connected := by
  let A := Finset.univ.filter (fun u => N u ∧ Avoids H {r} x u)
  obtain ⟨z,hz,hxz⟩ := ha r x hxr
  have hA : A.Nonempty := ⟨z,by simp [A,hz,hxz]⟩
  obtain ⟨u,hu,hmax⟩ := Finset.exists_max_image A (fun u => H.dist r u) hA
  obtain ⟨hNu,hxu⟩ := (Finset.mem_filter.mp hu).2
  have hur : u ≠ r := by simpa using Avoids.right H hxu
  refine ⟨u,hNu,hxu,?_⟩
  have hroot : r ∉ ({u} : Finset W) := by simp [hur.symm]
  have hcon := connected_delete_of_root H {u} r hroot
  have hall : ∀ y, y ∉ ({u} : Finset W) → Avoids H {u} r y := by
    intro y hy
    by_contra hn
    obtain ⟨z,hNz,hyz⟩ := ha u y (by simpa using hy)
    have hzu : z ≠ u := by simpa using Avoids.right H hyz
    have hnz : ¬ Avoids H {u} r z := fun hrz => hn (Avoids.trans H hrz (Avoids.symm H hyz))
    obtain ⟨hlt,huz⟩ := separator_distance H hc hur hzu.symm hnz
    have hzA : z ∈ A := by simp [A,hNz,Avoids.trans H hxu huz]
    exact (not_lt_of_ge (hmax z hzA)) hlt
  have he : {x : W | x ∉ ({u} : Finset W)} = {x | x ≠ u} := by ext x; simp
  rw [he] at hcon
  exact hcon hall

/-- Non-cut vertices in different branches at r can be deleted together. -/
theorem delete_two_noncut (hc : H.Connected) {r u w : W}
    (hur : u ≠ r) (hwr : w ≠ r) (hu : (H.induce {x | x ≠ u}).Connected)
    (hw : (H.induce {x | x ≠ w}).Connected) (hsep : ¬ Avoids H {r} u w) :
    (H.induce {x | x ∉ ({u,w} : Finset W)}).Connected := by
  apply connected_delete_of_root H {u,w} r (by simp [hur.symm,hwr.symm])
  intro y hy
  have hys : y ≠ u ∧ y ≠ w := by simpa using hy
  have hyu := hys.1
  have hyw := hys.2
  by_cases hyr : y = r
  · subst y
    exact Avoids.refl H (by simp [hur.symm,hwr.symm])
  by_cases hbranch : Avoids H {r} u y
  · obtain ⟨p,hp,hpu⟩ := Avoids.exists_path H (avoids_of_delete_connected H hu hur.symm hyu)
    have hnw : w ∉ p.support := by
      intro hwp
      have hwy : Avoids H {r} w y := ⟨p.dropUntil w hwp,fun z hz => by
        simp only [Finset.mem_singleton]
        intro he
        exact suffix_avoids_start H hp hwp hwr (he ▸ hz)⟩
      exact hsep (Avoids.trans H hbranch (Avoids.symm H hwy))
    refine ⟨p,?_⟩
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨by simpa using hpu z hz,fun he => hnw (he ▸ hz)⟩
  · obtain ⟨p,hp,hpw⟩ := Avoids.exists_path H (avoids_of_delete_connected H hw hwr.symm hyw)
    have hnu : u ∉ p.support := by
      intro hup
      apply hbranch
      exact ⟨p.dropUntil u hup,fun z hz => by
        simp only [Finset.mem_singleton]
        intro he
        exact suffix_avoids_start H hp hup hur (he ▸ hz)⟩
    refine ⟨p,?_⟩
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨fun he => hnu (he ▸ hz),by simpa using hpw z hz⟩

end Se20Insertion.FiniteConnectivity

namespace Se20Insertion.FiniteConnectivity
variable {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)

/-- In G-v, every component after another deletion meets N(v), since
G with that second vertex deleted is connected. -/
theorem deleted_attached (v : W) (hdel : ∀ u, (G.induce {z | z ≠ u}).Connected) :
    Attached (G.induce {z | z ≠ v}) (fun x => G.Adj v x.val) := by
  let H := G.induce {z | z ≠ v}
  intro u x hxu
  by_contra hn
  let T (z : W) : Prop := ∃ hz : z ≠ v, Avoids H {u} x ⟨z,hz⟩
  have hxouter : x.val ≠ u.val := fun he => hxu (Subtype.ext he)
  let J := G.induce {z | z ≠ u.val}
  have closed (a b : {z // z ≠ u.val}) (ha : T a.val) (hab : J.Adj a b) : T b.val := by
    obtain ⟨hav,hxa⟩ := ha
    have hb : b.val ≠ v := by
      intro hb
      apply hn
      refine ⟨⟨a.val,hav⟩,?_,hxa⟩
      change G.Adj v a.val
      simpa [J,hb] using hab.symm
    refine ⟨hb,Avoids.trans H hxa (Avoids.adj H (y := ⟨b.val,hb⟩) hab
      (Avoids.right H hxa) ?_)⟩
    simp only [Finset.mem_singleton]
    intro he
    exact b.prop (congrArg Subtype.val he)
  have go : ∀ {a b : {z // z ≠ u.val}}, J.Walk a b → T a.val → T b.val := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (closed a b ha hab)
  obtain ⟨p⟩ := hdel u.val ⟨x.val,hxouter⟩ ⟨v,u.prop.symm⟩
  have ht : T v := go p ⟨x.prop,Avoids.refl H (by simpa using hxu)⟩
  exact ht.choose rfl

theorem delete_pair_connected_iff (v : W) (u : {x // x ≠ v}) :
    ((G.induce {x | x ≠ v}).induce {x | x ≠ u}).Connected ↔
      (G.induce {x | x ∉ ({v,u.val} : Finset W)}).Connected := by
  let f : ((G.induce {x | x ≠ v}).induce {x | x ≠ u}) →g
      G.induce {x | x ∉ ({v,u.val} : Finset W)} :=
    { toFun := fun x => ⟨x.val.val,by
        simp only [Set.mem_ofPred_eq,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨x.val.prop,fun he => x.prop (Subtype.ext he)⟩⟩
      map_rel' := fun h => h }
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ≠ v ∧ x.val ≠ u.val := by simpa using x.prop
    exact ⟨⟨⟨x.val,hx.1⟩,fun he => hx.2 (congrArg Subtype.val he)⟩,rfl⟩
  let g : G.induce {x | x ∉ ({v,u.val} : Finset W)} →g
      ((G.induce {x | x ≠ v}).induce {x | x ≠ u}) :=
    { toFun := fun x => ⟨⟨x.val,by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using
        (show x.val ≠ v ∧ x.val ≠ u.val from by simpa using x.prop).1⟩,
        fun he => (show x.val ≠ u.val from (show x.val ≠ v ∧ x.val ≠ u.val from by simpa using x.prop).2)
          (congrArg Subtype.val he)⟩
      map_rel' := fun h => h }
  have hg : Function.Surjective g := by
    intro x
    exact ⟨f x,rfl⟩
  exact ⟨fun h => h.map f hf,fun h => h.map g hg⟩

/-- The correct finite non-separating-pair lemma: minimum degree three
excludes the cycle obstruction. The proof uses two farthest marked vertices,
and does not construct a block graph. -/
theorem exists_nonseparating_pair (hconn : G.Connected)
    (hdel : ∀ v, (G.induce {x | x ≠ v}).Connected)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    (hn : ∃ x y, x ≠ y ∧ ¬ G.Adj x y) :
    ∃ u w r, u ≠ w ∧ ¬ G.Adj u w ∧ G.Adj r u ∧ G.Adj r w ∧
      (G.induce {x | x ∉ ({u,w} : Finset W)}).Connected := by
  by_cases hall : ∀ v (u : {x // x ≠ v}), ((G.induce {x | x ≠ v}).induce {x | x ≠ u}).Connected
  · obtain ⟨u,w,r,huw,hnuw,hru,hrw⟩ := DegreeList.exists_induced_three_path G hconn hn
    exact ⟨u,w,r,huw,hnuw,hru,hrw,
      (delete_pair_connected_iff G u ⟨w,huw.symm⟩).mp (hall u ⟨w,huw.symm⟩)⟩
  push Not at hall
  obtain ⟨v,r,hr⟩ := hall
  let H := G.induce {x | x ≠ v}
  have hc : H.Connected := hdel v
  have hcard : 3 < (Finset.univ : Finset W).card := by
    have hlt := G.degree_lt_card_verts v
    have hdeg := hdegree v
    simpa only [Finset.card_univ] using (lt_of_le_of_lt hdeg hlt)
  have hpair : ({v,r.val} : Finset W).card < (Finset.univ : Finset W).card :=
    (Finset.card_insert_le _ _).trans_lt (by simp only [Finset.card_singleton]; omega)
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hpair
  have hz' : z ≠ v ∧ z ≠ r.val := by simpa using hz
  let x : {z // z ≠ v} := ⟨z,hz'.1⟩
  have hxr : x ≠ r := fun he => hz'.2 (congrArg Subtype.val he)
  have hnot : ∃ y : {z // z ≠ v}, y ≠ r ∧ ¬ Avoids H {r} x y := by
    by_contra! hy
    apply hr
    have hh := connected_delete_of_root H {r} x (by simpa using hxr)
      (fun y hy' => hy y (by simpa using hy'))
    change (H.induce {z : {z // z ≠ v} | z ∉ ({r} : Finset {z // z ≠ v})}).Connected at hh
    have he : ({z | z ∉ ({r} : Finset {z // z ≠ v})} : Set {z // z ≠ v}) = {z | z ≠ r} := by
      ext z; simp
    rw [he] at hh
    exact hh
  obtain ⟨y,hyr,hxy⟩ := hnot
  obtain ⟨u,hvu,hxu,hu⟩ := farthest_marked_noncut H hc _ (deleted_attached G v hdel) hxr
  obtain ⟨w,hvw,hyw,hw⟩ := farthest_marked_noncut H hc _ (deleted_attached G v hdel) hyr
  have hur : u ≠ r := by simpa using Avoids.right H hxu
  have hwr : w ≠ r := by simpa using Avoids.right H hyw
  have hsep : ¬ Avoids H {r} u w := fun huw =>
    hxy (Avoids.trans H (Avoids.trans H hxu huw) (Avoids.symm H hyw))
  have huw : u.val ≠ w.val := by
    intro he
    have he' : u = w := Subtype.ext he
    apply hsep
    rw [← he']
    exact Avoids.refl H (by simp [hur])
  have hnuw : ¬ G.Adj u.val w.val := fun ha => hsep
    (Avoids.adj H ha (by simp [hur]) (by simp [hwr]))
  have hrem := delete_two_noncut H hc hur hwr hu hw hsep
  have hpairN : ({u.val,w.val} : Finset W).card < (G.neighborFinset v).card := by
    have hb := Finset.card_insert_le u.val ({w.val} : Finset W)
    have hv := hdegree v
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    simp only [Finset.card_singleton] at hb
    omega
  obtain ⟨q,hqN,hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hpairN
  have hvq := (G.mem_neighborFinset _ _).mp hqN
  have hq' : q ≠ u.val ∧ q ≠ w.val := by simpa using hq
  let qH : {z // z ≠ v} := ⟨q,hvq.ne.symm⟩
  have hqH : qH ∉ ({u,w} : Finset {z // z ≠ v}) := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨fun he => hq'.1 (congrArg Subtype.val he),fun he => hq'.2 (congrArg Subtype.val he)⟩
  let J := G.induce {x | x ∉ ({u.val,w.val} : Finset W)}
  let f : (H.induce {x | x ∉ ({u,w} : Finset {z // z ≠ v})}) →g J :=
    { toFun := fun x => ⟨x.val.val,by
        have hx : x.val ≠ u ∧ x.val ≠ w := by simpa using x.prop
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨fun he => hx.1 (Subtype.ext he),fun he => hx.2 (Subtype.ext he)⟩⟩
      map_rel' := fun h => h }
  have hvJ : v ∉ ({u.val,w.val} : Finset W) := by simp [u.prop.symm,w.prop.symm]
  have reach (t : {x // x ∉ ({u.val,w.val} : Finset W)}) : J.Reachable ⟨v,hvJ⟩ t := by
    by_cases htv : t.val = v
    · have ht : t = ⟨v,hvJ⟩ := Subtype.ext htv
      rw [ht]
    · let tH : {z // z ≠ v} := ⟨t.val,htv⟩
      have htH : tH ∉ ({u,w} : Finset {z // z ≠ v}) := by
        have ht : t.val ≠ u.val ∧ t.val ≠ w.val := by simpa using t.prop
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨fun he => ht.1 (congrArg Subtype.val he),fun he => ht.2 (congrArg Subtype.val he)⟩
      exact (SimpleGraph.Adj.reachable (G := J) (u := ⟨v,hvJ⟩) (v := ⟨q,hq⟩) hvq).trans
        ((hrem ⟨qH,hqH⟩ ⟨tH,htH⟩).map f)
  exact ⟨u.val,w.val,v,huw,hnuw,hvu,hvw,
    { preconnected := fun x y => (reach x).symm.trans (reach y), nonempty := ⟨⟨v,hvJ⟩⟩ }⟩

end Se20Insertion.FiniteConnectivity
