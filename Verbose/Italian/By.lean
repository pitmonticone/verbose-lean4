import Verbose.Tactics.By
import Verbose.Italian.Common

open Lean Verbose.Italian

elab "Per " expr:maybeApplied " otteniamo " colGt news:newStuff : tactic => do
obtainTac (← maybeAppliedToTerm expr) (newStuffToArray news)

elab "Per " expr:maybeApplied " scegliamo " colGt news:newStuff : tactic => do
chooseTac (← maybeAppliedToTerm expr) (newStuffToArray news)

elab "Per " expr:maybeApplied " è sufficiente dimostrare " "che "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedToTerm expr) #[arg]

elab "Per " expr:maybeApplied " è sufficiente dimostrare " "che "? colGt "["args:term,*"]" : tactic => do
bySufficesTac (← maybeAppliedToTerm expr) args.getElems

lemma le_le_of_abs_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := en) cannotGet : CoreM String := pure "Impossibile dedurlo."

implement_endpoint (lang := en) theName : CoreM String := pure "Il nome"

implement_endpoint (lang := en) needName : CoreM String :=
pure "Devi fornire un nome per l'oggetto scelto."

implement_endpoint (lang := en) wrongNbGoals (actual announced : ℕ) : CoreM String :=
pure s!"Applicare questo porta a {actual} obiettivi, not {announced}."

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  Per h applicato a 0 otteniamo h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  Per h applicato a 0 e 0 otteniamo (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Per h otteniamo k tale che (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Per h otteniamo k tale che H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Per h otteniamo (hP : P) (hQ : Q)
  exact hQ

example (x : ℝ) (h : |x| ≤ 3) : True := by
  Per h otteniamo (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  Per h otteniamo (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Per h scegliamo g tale che (H : ∀ (y : ℕ), f (g y) = y)
  exact g

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Per h è sufficiente dimostrare che P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Per h è sufficiente dimostrare P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Per h è sufficiente dimostrare [P, R]
  exact hP
  exact hR

/-
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "Applicare questo porta a 0 obiettivi, non 1."
    Per h applicato a [0, 1] è sufficiente dimostrare P
  Per h applicato a 0 è sufficiente dimostrare P
  exact h'
 -/

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Per h applicato a 1 è sufficiente dimostrare 1 > 0
  norm_num

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "Il nome n è già utilizzato."
    Per h otteniamo n tale che H
  trivial
