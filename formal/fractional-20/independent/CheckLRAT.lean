import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

/-! Run the standard library's proved-sound checker on the exact saved files.
This IO execution is additional evidence, not a kernel proof of the concrete CNF,
and does not formalize the graph-to-CNF reduction. No native_decide is used. -/
open Std.Sat
open Std.Tactic.BVDecide

def loadCNF (path : System.FilePath) : IO (CNF Nat) := do
  let input ← IO.FS.Handle.mk path .read
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut clause : CNF.Clause Nat := .empty
  let mut header := false
  let mut nvars := 0
  let mut nclauses := 0
  repeat
    let raw ← input.getLine
    if raw.isEmpty then break
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then continue
    let parts := (line.splitOn " ").filter (· != "")
    if line.startsWith "p" then
      if header || clauses.size != 0 then throw (.userError "repeated/misplaced header")
      match parts with
      | ["p", "cnf", nv, nc] =>
        match nv.toNat?, nc.toNat? with
        | some v, some c => nvars := v; nclauses := c; header := true
        | _, _ => throw (.userError "bad CNF counts")
      | _ => throw (.userError "bad CNF header")
    else
      if !header then throw (.userError "missing CNF header")
      for part in parts do
        let some lit := part.toInt? | throw (.userError "bad literal")
        if lit == 0 then
          clauses := clauses.push clause
          clause := .empty
        else
          if lit.natAbs > nvars then throw (.userError "literal exceeds variable bound")
          clause := clause.add (lit.natAbs - 1) (lit > 0)
  if !header || clauses.size != nclauses || clause.size != 0 then
    throw (.userError "CNF counts or terminator mismatch")
  return ⟨clauses⟩

def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args | throw (.userError "usage: CheckLRAT cnf proof")
  let t0 ← IO.monoMsNow
  let cnf ← loadCNF cnfPath
  IO.println s!"Parsed {cnf.clauses.size} original clauses"
  let proof ← LRAT.loadLRATProof proofPath
  IO.println s!"Parsed {proof.size} LRAT actions"
  let ok := LRAT.check proof cnf
  let t1 ← IO.monoMsNow
  IO.println s!"Std.Tactic.BVDecide.LRAT.check = {ok}; elapsed_ms={t1-t0}"
  return if ok then 0 else 1

#print axioms Std.Tactic.BVDecide.LRAT.check_sound
