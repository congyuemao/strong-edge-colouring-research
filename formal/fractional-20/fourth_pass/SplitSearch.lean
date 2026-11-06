import fourth_pass.PackedSearch
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.AuxLemma
import Lean.Meta.Eval
import Lean.ToExpr

/-! An untrusted proof generator. Runtime evaluation proposes concrete states;
every proposed filter/transition equality is checked by the kernel, and each
search node is a theorem obtained from selectionSearch_split/prune. No native
reflection facility or axiom declaration is used. -/
namespace Se20Fractional.FourthPass.Packed
open Lean Meta Elab Tactic

instance : ToExpr State where
  toTypeExpr := mkConst ``State
  toExpr st := mkApp2 (mkConst ``State.mk) (toExpr st.graph) (toExpr st.chosen)

private def checked (type value : Expr) : MetaM Expr := do
  let name ← withOptions (fun o => o.setBool `Elab.async false) <|
    mkAuxLemma [] type value
  return mkConst name

private def checkedDecide (type : Expr) : MetaM Expr := do
  checked type (← mkDecideProof type)

private def checkedEq (lhs rhs : Expr) : MetaM Expr := do
  checked (← mkEq lhs rhs) (← mkEqRefl rhs)

private partial def makeSearchProof (n d fuel need : Nat) (st : Option State) (cs : List Edge)
    (counter : IO.Ref Nat) : MetaM Expr := do
  counter.modify (·+1)
  if fuel == 0 || need == 0 then throwError "The proposed search has an open leaf"
  let p := mkApp2 (mkConst ``possible) (toExpr n) (toExpr d)
  let t := mkApp2 (mkConst ``step) (toExpr n) (toExpr d)
  let stE := toExpr st
  let csE := toExpr cs
  let hn ← checkedDecide (mkNot (← mkEq (toExpr need) (toExpr (0 : Nat))))
  let vs := cs.filter (possible n d st)
  let filterE ← mkAppM ``List.filter #[mkApp p stE,csE]
  if vs.length < need then
    let hc ← checkedDecide (← mkLt (← mkAppM ``List.length #[filterE]) (toExpr need))
    let proof ← mkAppM ``selectionSearch_prune #[p,t,toExpr (fuel-1),toExpr need,stE,csE,hn,hc]
    return ← checked (← inferType proof) proof
  else
    match vs with
    | [] => throwError "Invalid empty viable list"
    | a::rest =>
      let next := step n d st a
      let hv ← checkedEq filterE (toExpr vs)
      let he ← checkedEq (mkApp2 t stE (toExpr a)) (toExpr next)
      let hskip ← makeSearchProof n d (fuel-1) need st rest counter
      let htake ← makeSearchProof n d (fuel-1) (need-1) next rest counter
      let proof ← mkAppM ``selectionSearch_split #[p,t,toExpr (fuel-1),toExpr need,stE,csE,
        toExpr a,toExpr rest,toExpr next,hn,hv,he,hskip,htake]
      return ← checked (← inferType proof) proof

unsafe def evalSplitSearch : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.getType
  let_expr Eq _ lhs _ := ty | throwError "Expected a Boolean search equality"
  unless lhs.isAppOfArity ``selectionSearch 8 do throwError "Expected selectionSearch"
  let args := lhs.getAppArgs
  let p := args[2]!
  unless p.isAppOfArity ``possible 2 do throwError "Expected packed possible predicate"
  let pa := p.getAppArgs
  let n ← evalExpr Nat (toTypeExpr Nat) pa[0]!
  let d ← evalExpr Nat (toTypeExpr Nat) pa[1]!
  let fuel ← evalExpr Nat (toTypeExpr Nat) args[4]!
  let need ← evalExpr Nat (toTypeExpr Nat) args[5]!
  let st ← evalExpr (Option State) (toTypeExpr (Option State)) args[6]!
  let cs ← evalExpr (List Edge) (toTypeExpr (List Edge)) args[7]!
  let counter ← IO.mkRef 0
  let proof ← makeSearchProof n d fuel need st cs counter
  goal.assign proof
  logInfo m!"Kernel-checked selection nodes: {← counter.get}"
  replaceMainGoal []

elab "split_selection" : tactic => unsafe evalSplitSearch
end Se20Fractional.FourthPass.Packed
