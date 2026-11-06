import fourth_pass.Relabel
import fourth_pass.SearchStatistics

namespace Se20Fractional.FourthPass.Packed
open Finset

def edgesGraph (n : Nat) : List Edge → Nat
  | [] => 0
  | e::es => addEdge n (edgesGraph n es) e

theorem edgesGraph_subset {n g : Nat} (es : List Edge)
    (he : ∀ e ∈ es, adjacent n g e.1 e.2 = true ∧ adjacent n g e.2 e.1 = true) :
    BitSubset (edgesGraph n es) g := by
  induction es with
  | nil => intro i hi; simp [edgesGraph] at hi
  | cons e es ih =>
    exact addEdge_subset (ih (fun f hf => he f (by simp [hf])))
      (he e (by simp)).1 (he e (by simp)).2

theorem edgesGraph_symm (n : Nat) (es : List Edge)
    (he : ∀ e ∈ es, e.1 < n ∧ e.2 < n) :
    ∀ a, a < n → ∀ b, b < n →
      adjacent n (edgesGraph n es) a b = adjacent n (edgesGraph n es) b a := by
  induction es with
  | nil => intros; simp [edgesGraph,adjacent,row]
  | cons e es ih =>
    exact addEdge_symm (ih (fun f hf => he f (by simp [hf])))
      (he e (by simp)).1 (he e (by simp)).2

theorem edgesGraph_adj {n a b : Nat} (es : List Edge) (ha : a < n) (hb : b < n)
    (he : ∀ e ∈ es, e.1 < n ∧ e.2 < n) :
    adjacent n (edgesGraph n es) a b = true ↔
      ∃ e ∈ es, (a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1) := by
  induction es with
  | nil => simp [edgesGraph,adjacent,row]
  | cons e es ih =>
    rw [edgesGraph,adjacent_addEdge ha hb (he e (by simp)).1 (he e (by simp)).2,
      ih (fun f hf => he f (by simp [hf]))]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨f,hf,h⟩ | h | h)
      · exact ⟨f,Or.inr hf,h⟩
      · exact ⟨e,Or.inl rfl,Or.inl h⟩
      · exact ⟨e,Or.inl rfl,Or.inr h⟩
    · rintro ⟨f,hf,h⟩
      rcases hf with rfl | hf
      · exact Or.inr h
      · exact Or.inl ⟨f,hf,h⟩

def starEdges (d : Nat) : List Edge := (List.range d).map (fun a => (0,a+1))
def innerPairs (d : Nat) : List Edge := (pairs (d+1)).filter (fun e => 0 < e.1)
def innerEdges (d m : Nat) : List Edge :=
  ((innerPairs d).zipIdx.filter (fun p => m.testBit p.2)).map Prod.fst
def typeEdges (d : Nat) (ts : List Nat) : List Edge :=
  ts.zipIdx.flatMap (fun (t,x) =>
    ((List.range d).filter (fun a => t.testBit a)).map (fun a => (a+1,d+1+x)))
def profileEdges (d m : Nat) (ts : List Nat) : List Edge :=
  starEdges d ++ innerEdges d m ++ typeEdges d ts
def profileGraph (d m : Nat) (ts : List Nat) : Nat := edgesGraph 14 (profileEdges d m ts)

theorem mem_pairs (n a b : Nat) : (a,b) ∈ pairs n ↔ a < n ∧ b < n ∧ a < b := by
  simp [pairs,and_assoc]

theorem mem_starEdges (d a b : Nat) : (a,b) ∈ starEdges d ↔ a = 0 ∧ 1 ≤ b ∧ b ≤ d := by
  simp only [starEdges,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨x,hx,ha,hb⟩
    omega
  · rintro ⟨rfl,hb,hd⟩
    exact ⟨b-1,by omega,rfl,by omega⟩

theorem mem_typeEdges (d : Nat) (ts : List Nat) (a b : Nat) :
    (a,b) ∈ typeEdges d ts ↔
      ∃ x, x < ts.length ∧ b = d+1+x ∧ 1 ≤ a ∧ a ≤ d ∧ (ts[x]?.getD 0).testBit (a-1) = true := by
  simp only [typeEdges,List.mem_flatMap,Prod.exists,List.mem_map,List.mem_filter,
    List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨t,x,ht,i,⟨hi,hti⟩,ha,hb⟩
    have hx : x < ts.length := by
      have hm := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp ht)
      exact hm.1
    have hxt : ts[x]?.getD 0 = t := by
      rw [List.mk_mem_zipIdx_iff_getElem?.mp ht]
      rfl
    refine ⟨x,hx,hb.symm,by omega,by omega,?_⟩
    have ha' : a-1 = i := by omega
    simpa [hxt,ha'] using hti
  · rintro ⟨x,hx,rfl,ha,had,ht⟩
    refine ⟨ts[x],x,?_,a-1,⟨by omega,?_⟩,by omega,rfl⟩
    · exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hx)
    · simpa [List.getElem?_eq_getElem hx] using ht

#print axioms edgesGraph_adj
end Se20Fractional.FourthPass.Packed
