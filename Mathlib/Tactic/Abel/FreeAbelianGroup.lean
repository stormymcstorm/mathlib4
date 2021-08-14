import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Lean.Elab.Command
import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Abel.ToExprInt

def List.get2 {A : Type _} [Zero A] : List A → ℕ → A
| [],     n     => 0
| (a::l), (n+1) => get2 l n
| (a::l), 0     => a

variable {A : Type u}

instance : Zero ℕ := ⟨0⟩
instance : Zero ℤ := ⟨0⟩

def FreeAbelianGroup : Type := List (ℤ × ℕ)

namespace FreeAbelianGroup

variable {A} [HAdd A A A] [DecidableEq A] [HMul A A A] [OfNat A 0]
/-- The letters in the free abelian group are indexed by ℕ. It
is implemented as `FreeAbelianGroup A`, where `A` is either `ℕ` or `ℤ` for
the coefficients and `ℕ` is an indexing type for the letters.
We only use normalized elements of the free abelian group which
means the elements of the `List` are sorted by the letter index,
and the same letter does not appear twice in the `List`. -/
-- Marked `noncomputable` because Lean couldn't compile `List.rec` at the time of writing
protected noncomputable def add (a : FreeAbelianGroup) : FreeAbelianGroup → FreeAbelianGroup :=
@List.rec (ℤ × ℕ) (λ a : FreeAbelianGroup => FreeAbelianGroup → FreeAbelianGroup)
  id
  (λ nx₁ a₁ ih₁ a₂ => -- ih₁ adds a₁
    @List.rec (ℤ × ℕ) (λ a : FreeAbelianGroup => FreeAbelianGroup → FreeAbelianGroup)
      id
      (λ nx₂ a₂ ih₂ he₁ =>
        if nx₁.2 < nx₂.2
          then nx₁ :: ih₁ (nx₂ :: a₂)
          else if nx₁.2 ≠ nx₂.2
            then nx₂ :: ih₂ he₁
            else let n : ℤ := nx₁.1 + nx₂.1
              if n = 0
                then ih₁ a₂
                else (n, nx₁.2) :: ih₁ a₂)
      a₂ (nx₁ :: a₁))
  a

/-- More readable version of `add`. made `unsafe` at the time of writing because there
was no well founded recursion. Necessary because lean could not compile `List.rec` at the
time of writing, so `add` does not compile. -/
unsafe def add' : FreeAbelianGroup → FreeAbelianGroup → FreeAbelianGroup
| l,                  []                 => l
| [],                 l                  => l
| he₁@((n₁, x₁)::a₁), he₂@((n₂, x₂)::a₂) =>
  if x₁ < x₂
    then (n₁, x₁) :: add' a₁ he₂
    else if x₁ ≠ x₂
      then (n₂, x₂) :: add' a₂ he₁
      else
        let n := n₁ + n₂
        if n = 0
          then add' a₁ a₂
          else (n, x₁) :: add' a₁ a₂

def gsmul (n : ℤ) : FreeAbelianGroup → FreeAbelianGroup
| []          => []
| ((m, x)::l) => (n * m, x) :: gsmul n l

def nsmul (n : ℕ) : FreeAbelianGroup → FreeAbelianGroup
| []          => []
| ((m, x)::l) => (n * m, x) :: nsmul n l

def neg : FreeAbelianGroup → FreeAbelianGroup
| []          => []
| ((m, x)::l) => (- m, x) :: neg l

instance : Zero FreeAbelianGroup := ⟨[]⟩
noncomputable instance : Add FreeAbelianGroup := ⟨FreeAbelianGroup.add⟩
instance : Neg FreeAbelianGroup := ⟨FreeAbelianGroup.neg⟩
noncomputable instance : Sub FreeAbelianGroup := ⟨λ x y => x + -y⟩

variable {B : Type _}

def eval [AddCommGroup B] (l : List B) : FreeAbelianGroup → B
| []          => 0
| ((n, x)::e) => gsmul_rec n (l.get2 x) + eval l e

lemma evalAdd [AddCommGroup B] (l : List B) : ∀ (e₁ e₂ : FreeAbelianGroup),
  eval l (e₁ + e₂) = eval l e₁ + eval l e₂ := sorry

lemma evalSmul [AddCommGroup B] (l : List B) : ∀ (n : ℤ) (e : FreeAbelianGroup),
  eval l (gsmul n e) = gsmul_rec n (eval l e) := sorry

open Lean Meta

instance : ToExpr (List ℕ) := inferInstance

instance : ToExpr FreeAbelianGroup :=
{ toExpr := λ l => mkApp2
    (mkConst `id [levelOne])
    (mkConst `FreeAbelianGroup)
    (@ToExpr.toExpr (List (ℤ × ℕ)) _ l),
  toTypeExpr := mkConst `FreeAbelianGroup  }


end FreeAbelianGroup
