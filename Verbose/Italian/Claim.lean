import Verbose.Tactics.Lets
import Verbose.Italian.Common

open Lean Verbose.Italian

macro ("Fatto" <|> "Affermazione") name:ident ":" stmt:term "per" colGt prf:tacticSeq: tactic => `(tactic|have $name : $stmt := by $prf)

open Lean Elab Tactic

elab ("Fatto" <|> "Affermazione") name:ident ":" stmt:term "from" prf:maybeApplied : tactic => do
  let prfTerm ← maybeAppliedToTerm prf
  evalTactic (← `(tactic|have $name : $stmt := by exact $prfTerm))

example : 1 = 1 := by
  Affermazione H : 1 = 1 per
    rfl
  exact H

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Fatto key : n + n = 2*n per
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fatto key : 0 < 2*n per
    linarith only [h]
  Fatto keybis : 0 < 2*n from mul_pos applicato a zero_lt_two e h
  trivial
