import Mathlib.tactic.Abel.GroupExpr
import Init.Control.State
import Init.Data.Array.Basic
import Lean.Elab.Term

open Lean Meta Lean.Elab.Term

/-- Check if `e` is def eq to an `Expr` in the `Array Expr` in the state. If
it is, then return the index, if not, then add it to the `Array` and return its index
in the new array. -/
def addAtom (e : Expr) : StateT (Array Expr) TermElabM ℕ :=
do match (← (← StateT.get).findIdxM? (λ e' => isDefEq e e')) with
   | some n => return n
   | none   => StateT.modifyGet (λ a => (a.size + 1, a.push e))

/-- Convert an `Expr` into a `GroupExpr`, whilst maintaining
a list of atoms.  -/
unsafe def ExprToGroupExprAux : Expr → StateT (Array Expr) TermElabM GroupExpr
| e => e.withApp fun f args => do
  if f.isConstOf ``HAdd.hAdd
    then
      let #[_, _, _, _, a, b] ← args | throwError "fail"
      return ((← ExprToGroupExprAux a) + (← ExprToGroupExprAux b))
    else if f.isConstOf ``Zero.zero
      then return 0
      else if f.isConstOf ``nsmul_rec
        then
          let #[_, _, _, n, a] ← args | throwError "fail"
          return (GroupExpr.nsmul (← evalExpr ℕ `Nat n) (← ExprToGroupExprAux a))
        else if f.isConstOf ``gsmul_rec
          then
            let #[_, _, _, n, a] ← args | throwError "fail"
            return (GroupExpr.gsmul (← evalExpr ℤ `Int n) (← ExprToGroupExprAux a))
          else if f.isConstOf ``Neg.neg
            then
              let #[_, _, a] ← args | throwError "fail"
              return (-(← ExprToGroupExprAux a))
            else if f.isConstOf ``HSub.hSub
              then
                let #[_, _, _, _, a, b] ← args | throwError "fail"
                return ((← ExprToGroupExprAux a) - (← ExprToGroupExprAux b))
              else
                return (GroupExpr.atom (← addAtom e))

unsafe def ExprToGroupExpr (e : Expr) : TermElabM (GroupExpr × Array Expr) :=
StateT.run (ExprToGroupExprAux e) Array.empty
