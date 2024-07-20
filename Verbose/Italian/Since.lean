import Verbose.Tactics.Since
import Verbose.Italian.Common
import Lean

namespace Verbose.Italian

open Lean Elab Tactic

elab "Siccome " facts:facts " otteniamo " news:newObject : tactic => do
  let newsT ← newObjectToTerm news
  let news_patt := newObjectToRCasesPatt news
  let factsT := factsToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Siccome " facts:facts " otteniamo " news:newFacts : tactic => do
  let newsT ← newFactsToTypeTerm news
  let news_patt := newFactsToRCasesPatt news
  let factsT := factsToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Siccome " facts:facts " concludiamo che " concl:term : tactic => do
  let factsT := factsToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab "Siccome " facts:facts " è sufficiente dimostrare " " che " newGoals:facts : tactic => do
  let factsT := factsToArray facts
  let newGoalsT := factsToArray newGoals
  sinceSufficesTac factsT newGoalsT

implement_endpoint (lang := en) couldNotProve (goal : Format) : CoreM String :=
pure s!"Could not prove:\n {goal}"

implement_endpoint (lang := en) failedProofUsing (goal : Format) : CoreM String :=
pure s!"Failed to prove this using the provided facts.\n{goal}"

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Siccome ∃ k, n = 2*k otteniamo k tale che H : n = 2*k
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  Siccome ∀ n ≥ N, ∃ k, n = 2*k e n ≥ N otteniamo k tale che H : n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Siccome P ∧ Q otteniamo (hP : P) e (hQ : Q)
  exact hQ

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Siccome ∀ n ≥ 3, P n e n ≥ 3 otteniamo H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Siccome ∀ n ≥ 3, P n ∧ Q n e n ≥ 3 otteniamo H : P n e H' : Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Siccome ∀ n ≥ 3, P n e n ≥ 3 concludiamo che P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Siccome ∀ n ≥ 3, P n ∧ Q n e n ≥ 3 concludiamo che P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Siccome ∀ n ≥ 3, P n ∧ Q n e n ≥ 3 otteniamo H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Siccome ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n e n ≥ 3 otteniamo H : P n e H' : Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Siccome P → Q è sufficiente dimostrare che P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Siccome P → R → Q è sufficiente dimostrare che P e R
  constructor
  exact hP
  exact hR
