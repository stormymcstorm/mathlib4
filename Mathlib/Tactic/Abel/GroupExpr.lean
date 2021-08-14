import Mathlib.Tactic.Abel.FreeAbelianGroup

variable (A : Type)

inductive GroupExpr : Type
| atom : Nat → GroupExpr
| nsmul : Nat → GroupExpr → GroupExpr
| gsmul : Int → GroupExpr → GroupExpr
| neg : GroupExpr → GroupExpr
| sub : GroupExpr → GroupExpr → GroupExpr
| zero : GroupExpr
| add : GroupExpr → GroupExpr → GroupExpr

namespace GroupExpr

instance : Add GroupExpr := ⟨GroupExpr.add⟩
instance : Zero GroupExpr := ⟨GroupExpr.zero⟩
instance : Neg GroupExpr := ⟨GroupExpr.neg⟩
instance : Sub GroupExpr := ⟨GroupExpr.sub⟩

variable {B : Type u}

def eval
  [Add B] [Neg B] [Sub B] [Zero B]
  (ns : ℕ → B → B)
  (gs : ℤ → B → B)
  (l : List B) : GroupExpr → B
| atom n    => List.get2 l n
| nsmul n e => ns n (eval ns gs l e)
| gsmul n e => gs n (eval ns gs l e)
| add e₁ e₂ => eval ns gs l e₁ + eval ns gs l e₂
| neg e     => -eval ns gs l e
| sub e₁ e₂ => eval ns gs l e₁ - eval ns gs l e₂
| zero      => 0

noncomputable def evalF : GroupExpr → FreeAbelianGroup
| atom n    => [(1, n)]
| nsmul n e => FreeAbelianGroup.nsmul n (evalF e)
| gsmul n e => FreeAbelianGroup.gsmul n (evalF e)
| add e₁ e₂ => evalF e₁ + evalF e₂
| neg e     => -evalF e
| sub e₁ e₂ => evalF e₁ - evalF e₂
| zero      => 0

unsafe def evalF' : GroupExpr → FreeAbelianGroup
| atom n    => [(1, n)]
| nsmul n e => FreeAbelianGroup.nsmul n (evalF' e)
| gsmul n e => FreeAbelianGroup.gsmul n (evalF' e)
| add e₁ e₂ => (evalF' e₁).add' (evalF' e₂)
| neg e     => -evalF' e
| sub e₁ e₂ => (evalF' e₁).add' (-evalF' e₂)
| zero      => 0

open Lean Lean.Elab.Term Meta

def toExpr : GroupExpr → Expr
| atom n => mkApp (mkConst ``GroupExpr.atom) (ToExpr.toExpr n)
| nsmul n e => mkApp2 (mkConst ``GroupExpr.nsmul) (ToExpr.toExpr n) (toExpr e)
| gsmul n e => mkApp2 (mkConst ``GroupExpr.gsmul) (ToExpr.toExpr n) (toExpr e)
| add e₁ e₂ => mkApp2 (mkConst ``GroupExpr.add) (toExpr e₁) (toExpr e₂)
| neg e => mkApp (mkConst ``GroupExpr.neg) (toExpr e)
| sub e₁ e₂ => mkApp2 (mkConst ``GroupExpr.sub) (toExpr e₁) (toExpr e₂)
| zero => mkConst ``GroupExpr.zero []

instance : ToExpr GroupExpr :=
{ toExpr := toExpr,
  toTypeExpr := mkConst ``GroupExpr }

end GroupExpr
