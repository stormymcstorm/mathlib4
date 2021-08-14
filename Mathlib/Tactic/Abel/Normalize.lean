import Mathlib.Tactic.Abel.Atoms
import Lean.Meta.SynthInstance
import Lean.Elab.Tactic

def nth {A : Type u} [Zero A] : ℕ → List A → A
| _,   []   => 0
| 0,   a::l => a
| n+1, a::l => nth n l

open Lean Meta Lean.Elab.Term

namespace Abel

structure Cache : Type :=
(G : Expr)
(inst : Expr)
(univ : Level)

def mkCache (e : Expr) : TermElabM Abel.Cache := do
let G ← inferType e
let u ← getLevel G
let i ← synthInstance (mkApp (mkConst `AddCommGroup [u]) G)
return ⟨G, i, u⟩

/-- Turn an `Array Expr` containing the atoms into an `Expr` of a `List` of the `Atoms` -/
def mkListAtoms (a : Array Expr) (c : Abel.Cache) : Expr :=
a.foldr (λ atom list => mkApp3 (mkConst `List.cons [c.univ]) c.G atom list)
  (mkApp (mkConst ``List.nil [c.univ]) c.G)

-- Decision - how to normalize these things? Do I leave it as the evaluation of a
-- FreeAbelianGroup or not? Answer : leave it for now. Normalize using simp later.

-- Need to reflect GroupExpr and FreeAbelianGroup

lemma normalizeLemma {A : Type u} [AddCommGroup A]
  (g : GroupExpr)
  (f : FreeAbelianGroup)
  (a : A)
  (l : List A)
  (hga : g.eval AddMonoid.nsmul AddGroup.gsmul l = a)
  (hgf : g.evalF = f) : a = f.eval l := sorry

/--Takes an `Expr` and returns a normalized `Expr` and a proof
of equality with the normalized expression. -/
unsafe def normalize (e : Expr) : TermElabM (Expr × Expr) :=
do
let ⟨g, a⟩ ← ExprToGroupExpr e
let c ← mkCache e
let l ← mkListAtoms a c
let f ← g.evalF'
let fe ← toExpr f
let newTerm : Expr :=
  mkApp4
    (mkConst ``FreeAbelianGroup.eval [c.univ])
    c.G
    c.inst
    l
    fe
let proof : Expr :=
  mkApp8
    (mkConst ``normalizeLemma [c.univ])
    c.G
    c.inst
    (toExpr g)
    fe
    e
    l
    (← mkEqRefl e)
    (← mkEqRefl fe)
return (proof, newTerm)

end Abel
