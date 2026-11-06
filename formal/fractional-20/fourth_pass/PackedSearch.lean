import fourth_pass.SelectionSearch

/-! Computational prototype. Graph-level soundness is NOT yet proved in this
module. All recursion is structural or explicitly fuelled. -/
namespace Se20Fractional.FourthPass.Packed

abbrev Edge := Nat × Nat
structure State where
  graph : Nat
  chosen : List Edge
  deriving Repr

def bit (i : Nat) : Nat := 1 <<< i
def mask (n : Nat) : Nat := bit n - 1
def row (n h a : Nat) : Nat := (h >>> (n*a)) &&& mask n
def adjacent (n h a b : Nat) : Bool := (row n h a &&& bit b) != 0
def addEdge (n h : Nat) (e : Edge) : Nat :=
  h ||| bit (n*e.1+e.2) ||| bit (n*e.2+e.1)
def pop : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, x => if x == 0 then 0 else 1 + pop k (x &&& (x-1))
def internal (n h r : Nat) : Nat → Nat
  | 0 => 0
  | a+1 => internal n h r a +
      if (r &&& bit a) == 0 then 0 else pop n (row n h a &&& r &&& mask a)
def low (n h : Nat) (e : Edge) : Bool :=
  let a := row n h e.1
  let b := row n h e.2
  let t := pop n (a &&& b)
  t ≤ 1 && 4*t + internal n h ((a ||| b) &&& (mask n ^^^ bit e.1 ^^^ bit e.2)) n ≤ 4
def valid (n : Nat) (st : State) : Bool :=
  (List.range n).all (fun a => pop n (row n st.graph a) ≤ 4) &&
  st.chosen.all (low n st.graph)
def conflict (n h : Nat) (e f : Edge) : Bool :=
  ((bit e.1 ||| bit e.2 ||| row n h e.1 ||| row n h e.2) &&&
    (bit f.1 ||| bit f.2)) != 0
def witnesses (n d h : Nat) (e f : Edge) : List Edge :=
  [(e.1,f.1),(e.1,f.2),(e.2,f.1),(e.2,f.2)].filter (fun p =>
    d < p.1 && d < p.2 && p.1 != p.2 &&
    pop n (row n h p.1) < 4 && pop n (row n h p.2) < 4)
def forcePair (n d : Nat) (h : Option Nat) (e f : Edge) : Option Nat :=
  match h with
  | none => none
  | some g =>
    if conflict n g e f then some g else
    match witnesses n d g e f with
    | [] => none
    | [p] => some (addEdge n g p)
    | _ => some g
def forceOne (n d : Nat) (e : Edge) (h : Option Nat) : List Edge → Option Nat
  | [] => h
  | f :: fs => forceOne n d e (forcePair n d h e f) fs
def forceAll (n d : Nat) (h : Option Nat) : List Edge → Option Nat
  | [] => h
  | e :: es => forceAll n d (forceOne n d e h es) es
def propagate (n d : Nat) : Nat → State → Option State
  | 0, st => if valid n st then some st else none
  | fuel+1, st =>
    if !valid n st then none else
    match forceAll n d (some st.graph) st.chosen with
    | none => none
    | some g => if g == st.graph then some st else
        propagate n d fuel { st with graph := g }
def extend (n d : Nat) (st : State) (e : Edge) : Option State :=
  propagate n d 10 { graph := addEdge n st.graph e, chosen := e :: st.chosen }
def possible (n d : Nat) (st : Option State) (e : Edge) : Bool :=
  match st with
  | none => false
  | some s => (extend n d s e).isSome
def step (n d : Nat) (st : Option State) (e : Edge) : Option State :=
  st.bind (fun s => extend n d s e)

def rootGraph (n d : Nat) : Nat :=
  (List.range d).foldl (fun h a => addEdge n h (0,a+1)) 0
def typeGraph (n d : Nat) (ts : List Nat) : Nat :=
  (ts.zipIdx).foldl (fun h (t,x) =>
    (List.range d).foldl (fun g a =>
      if (t &&& bit a) != 0 then addEdge n g (d+1+x,a+1) else g) h) (rootGraph n d)
def rootChosen (s : Nat) : List Edge := (List.range s).map (fun a => (0,a+1))
def pairs (n : Nat) : List Edge :=
  (List.range n).flatMap (fun a => ((List.range n).filter (fun b => a < b)).map (a,·))
def candidates (n d s h : Nat) (ts : List Nat) : List Edge :=
  (pairs n).filter (fun e => 0 < e.1 &&
    (if e.1 ≤ d then adjacent n h e.1 e.2 else
      ((ts[e.1-d-1]?.getD 0 ||| ts[e.2-d-1]?.getD 0) &&& mask s) == mask s))
def checkProfile (d s inner : Nat) (ts : List Nat) : Bool :=
  let n := d+1+ts.length
  let h := typeGraph n d ts ||| inner
  let st : State := ⟨h,rootChosen s⟩
  if !valid n st then true else
  selectionSearch (possible n d) (step n d) 92 (16-s) (some st)
    (candidates n d s h ts)

end Se20Fractional.FourthPass.Packed
