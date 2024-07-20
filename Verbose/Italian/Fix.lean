import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Sia₁ " colGt fixDecl : tactic
syntax "Sia " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)

elab_rules : tactic
  | `(tactic| Sia₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Sia₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Sia₁ $decl:fixDecl))


macro_rules
  | `(tactic| Sia $decl:fixDecl) => `(tactic| Sia₁ $decl)

macro_rules
  | `(tactic| Sia $decl:fixDecl $decls:fixDecl*) => `(tactic| Sia₁ $decl; Sia $decls:fixDecl*)

implement_endpoint (lang := en) noObjectIntro : CoreM String :=
pure "Non c'è alcun oggetto da introdurre qui."

implement_endpoint (lang := en) noHypIntro : CoreM String :=
pure "Non c'è alcuna ipotesi da introdurre qui."

implement_endpoint (lang := en) negationByContra (hyp : Format) : CoreM String :=
pure s!"L'obiettivo è già una negazione, dimostrarlo per assurdo non porta a nulla. \
 Puoi assumere direttamente {hyp}."

implement_endpoint (lang := en) wrongNegation : CoreM String :=
pure "Non è questo ciò che si deve supporre per assurdo, anche dopo aver svolto la negazione."

macro_rules
| `(ℕ) => `(Nat)

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Sia b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sia (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sia (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sia n
  success_if_fail_with_msg "Non c'è alcun oggetto da introdurre qui."
    Sia h
  intro hn
  Sia k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/-
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Sia (n > 0)
  success_if_fail_with_msg ""
    Sia n
  Sia k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Sia n > 0
  success_if_fail_with_msg ""
    Sia n
  Sia k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Sia n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Sia n ∈ A
  trivial
