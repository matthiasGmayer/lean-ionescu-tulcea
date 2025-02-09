import Lean
import Mathlib.Tactic.Common
import Mathlib

open Lean Meta Elab Term Parser Tactic

@[term_parser] def simp := leading_parser
  "simp% " >> Lean.Parser.termParser Lean.Parser.maxPrec

@[term_elab simp] def elabSimp : TermElab := fun stx _ => do
  let e ← elabTermAndSynthesize stx[1] none
  let (rhs, g) ← Conv.mkConvGoalFor e
  let out ← Tactic.run g.mvarId! do
    evalTactic (← `(tactic|simp))
    for mvarId in ← getGoals do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    let e' ← instantiateMVars rhs
  return rhs

#simp 2 + 2
#check simp% (2 + 2)

variable (α : ℕ -> Type*) (n m : ℕ)
variable (x : ((fun (J : Set ℕ)  => (k : J) → α k) {k | n < k ∧ k ≤ n + m + 1}))
#check x
#check type_of% x
def x' := by simp at x; exact x
#check x'
#check simp% x
#check simp% type_of% x
#check type_of% (simp% x)
-- this should have the same type as x'
