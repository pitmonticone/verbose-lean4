import Verbose.Tactics.Lets
import Mathlib.Tactic.Linarith

elab "Dimostriamo" " per induzione" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

open Lean Elab Tactic in

macro "Dimostriamo" " che " stmt:term :tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt)

declare_syntax_cat explicitStmtEN
syntax ": " term : explicitStmtEN

def toStmt (e : Lean.TSyntax `explicitStmtEN) : Lean.Term := ⟨e.raw[1]!⟩

elab "Dimostriamo" " che " witness:term " funziona" stmt:(explicitStmtEN)?: tactic => do
  useTac witness (stmt.map toStmt)

elab "Dimostriamo" " prima che " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Dimostriamo" " ora che " stmt:term : tactic =>
  unblockTac stmt

syntax "Devi annunciare: Dimostriamo ora che " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(Devi annunciare: Dimostriamo ora che $stx)

macro "Dimostriamo" " una contraddizione" : tactic => `(tactic|exfalso)

open Lean

implement_endpoint (lang := en) inductionError : CoreM String :=
pure "La proposizione deve iniziare con un quantificatore universale su un numero naturale."

implement_endpoint (lang := en) notWhatIsNeeded : CoreM String :=
pure "Questo non è ciò che si deve dimostrare."

implement_endpoint (lang := en) notWhatIsRequired : CoreM String :=
pure "Questo non è ciò che è richiesto ora."

example : 1 + 1 = 2 := by
  Dimostriamo che 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Dimostriamo che 2 funziona
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Dimostriamo che 2 funziona: 4 = 2*2
  rfl

example : True ∧ True := by
  Dimostriamo prima che True
  trivial
  Dimostriamo ora che True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Dimostriamo che P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Dimostriamo che Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Dimostriamo prima che 0 = 0
  trivial
  Dimostriamo ora che 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Dimostriamo prima che 0 = 0
  trivial
  Dimostriamo ora che 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Dimostriamo prima che 1 = 1
  trivial
  Dimostriamo ora che 0 = 0
  trivial

example : True ↔ True := by
  Dimostriamo prima che True → True
  exact id
  Dimostriamo ora che True → True
  exact id

example (h : False) : 2 = 1 := by
  Dimostriamo una contraddizione
  exact h

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Dimostriamo per induzione H : ∀ k, P k
  . exact h₀
  . exact h k hyp_rec
  . exact H 4

/-
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "La proposizione deve iniziare con un quantificatore universale su un numero naturale."
    Dimostriamo per induzione H : true
  Dimostriamo per induzione H : ∀ n, P n
  exact h₀
  exact h

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : true := by
  Dimostriamo per induzione H : ∀ k, P k
  exacts [h₀, h, trivial]

example : true := by
  Dimostriamo per induzione H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial
-/

set_option linter.unusedVariables false in
example : true := by
  success_if_fail_with_msg "La proposizione deve iniziare con un quantificatore universale su un numero naturale."
    Dimostriamo per induzione H : true
  success_if_fail_with_msg "La proposizione deve iniziare con un quantificatore universale su un numero naturale."
    Dimostriamo per induzione H : ∀ n : ℤ, true
  trivial
