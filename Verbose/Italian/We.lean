import Verbose.Tactics.We
import Verbose.Italian.Common

open Lean Elab Parser Tactic Verbose.Italian

declare_syntax_cat becomes
syntax colGt " che diventa " term : becomes

def extractBecomes (expr : Lean.TSyntax `becomes) : Lean.Term := ⟨expr.raw[1]!⟩

elab rw:"Noi" " riscriviamo usando " s:myRwRuleSeq l:(location)? new:(becomes)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomes)

elab rw:"Noi" " riscriviamo usando " s:myRwRuleSeq " ovunque" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "Noi" " procediamo usando " exp:term : tactic =>
  discussOr exp

elab "Noi" " procediamo dipendendo da " exp:term : tactic =>
  discussEm exp

elab "Noi" " concludiamo per " expr:maybeApplied : tactic => do
  concludeTac (← maybeAppliedToTerm expr)

elab "Noi" " combiniamo [" prfs:term,* "]" : tactic => do
  combineTac prfs.getElems

elab "Noi" " calcoliamo" loc:(location)? : tactic => do
  computeTac loc

elab "Noi" " applichiamo " exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

elab "Noi" " applichiamo " exp:term " ad " h:ident: tactic => do
  let loc ← ident_to_location h
  evalTactic (← `(tactic|apply_fun $exp $loc:location))

elab "Noi" " applichiamo " exp:term " al termine " expr:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $expr))

macro "Noi" " dimentichiamo " args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "Noi" " riformuliamo " h:ident " come " new:term : tactic => `(tactic|change $new at $h:ident)

elab "Noi" " contrapponiamo" : tactic => contraposeTac true

elab "Noi" " contrapponiamo" " semplicemente": tactic => contraposeTac false

elab "Noi " " svolgiamo la negazione " l:(location)? new:(becomes)? : tactic => do
  pushNegTac (l.map expandLocation) (new.map extractBecomes)

implement_endpoint (lang := en) rwResultWithoutGoal : CoreM String :=
pure "Specificare il risultato della riscrittura è possibile solo quando rimane qualcosa da provare."

implement_endpoint (lang := en) rwResultSeveralLoc : CoreM String :=
pure "Specificare il risultato della riscrittura è possibile solo quando si riscrive in una singola posizione."

implement_endpoint (lang := en) cannotContrapose : CoreM String :=
pure "Non si può contrappore: l'obiettivo principale non è un'implicazione."

example (P Q : Prop) (h : P ∨ Q) : True := by
  Noi procediamo usando h
  . intro _hP
    trivial
  . intro _hQ
    trivial

example (P : Prop) : True := by
  Noi procediamo dipendendo da P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "application type mismatch
  hRP hQ
argument
  hQ
has type
  Q : Prop
but is expected to have type
  R : Prop"
    Noi concludiamo per hRP applicato a hQ
  Noi concludiamo per hRP applicato a hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Noi concludiamo per h applicato a _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Noi concludiamo per h

example {a b : ℕ}: a + b = b + a := by
  Noi calcoliamo

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  Noi calcoliamo at h
  Noi concludiamo per h

variable (k : Nat)

example (h : True) : True := by
  Noi concludiamo per h

example (h : ∀ _n : ℕ, True) : True := by
  Noi concludiamo per h applicato a 0

example (h : True → True) : True := by
  Noi applichiamo h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  Noi concludiamo per h applicato a 0 e 1

example (a b : ℕ) (h : a < b) : a ≤ b := by
  Noi concludiamo per h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  Noi concludiamo per h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  Noi combiniamo [h, h']

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  Noi combiniamo [h, h']

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  Noi combiniamo [h, h']

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Noi riscriviamo usando ← h
  Noi concludiamo per h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Noi riscriviamo usando h at h'
  Noi concludiamo per h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Noi riscriviamo usando ← h at h' che diventa a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Noi riscriviamo usando ← h at h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  Noi riscriviamo usando h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  Noi riscriviamo usando h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "Il termine fornito
  a = c
non è uguale per definizione a quello atteso
  b = c"
    Noi riscriviamo usando [h] at h' che diventa a = c
  Noi riscriviamo usando [h] at h' che diventa b = c
  Noi concludiamo per h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  Noi riscriviamo usando h ovunque
  Noi concludiamo per h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Noi applichiamo h al termine h'
  Noi concludiamo per h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  Noi concludiamo per h applicato a hP e hQ

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  Noi applichiamo f ad h
  Noi concludiamo per h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Noi applichiamo h al termine 0
  Noi concludiamo per h


example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Noi contrapponiamo
  intro h
  use x/2
  constructor
  Noi concludiamo per h
  Noi concludiamo per h

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by Noi concludiamo per h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by Noi concludiamo per h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by Noi concludiamo per h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by Noi concludiamo per h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by Noi concludiamo per h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Noi contrapponiamo semplicemente
  intro h
  Noi svolgiamo la negazione
  Noi svolgiamo la negazione at h
  use x/2
  constructor
  · Noi concludiamo per h
  · Noi concludiamo per h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Noi contrapponiamo semplicemente
  intro h
  success_if_fail_with_msg "Il termine fornito
  0 < x
non è uguale per definizione a quello atteso
  ∃ ε > 0, ε < x"
    Noi svolgiamo la negazione che diventa 0 < x
  Noi svolgiamo la negazione che diventa ∃ ε > 0, ε < x
  success_if_fail_with_msg "Il termine fornito
  ∃ ε > 0, ε < x
non è uguale per definizione a quello atteso
  0 < x"
    Noi svolgiamo la negazione at h che diventa ∃ ε > 0, ε < x
  Noi svolgiamo la negazione at h che diventa 0 < x
  use x/2
  constructor
  · Noi concludiamo per h
  · Noi concludiamo per h

set_option linter.unusedVariables false in
example : (∀ n : ℕ, False) → 0 = 1 := by
  Noi contrapponiamo
  Noi calcoliamo

example (P Q : Prop) (h : P ∨ Q) : True := by
  Noi procediamo usando h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  Noi procediamo dipendendo da P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

/-
namespace Verbose.Italian

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  Noi unfold f
  refl

example (h : f 2 = 4) : True → True := by
  Noi unfold f at h
  guard_hyp_strict h : 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg ""
    Noi unfold f at h che diventa 2*2 = 5
  Noi unfold f at h che diventa 2*2 = 4
  exact id

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Noi rename n to p at h
  Noi rename k to l at h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Noi rename n to p at h che diventa ∀ p, ∃ k, P p k
  success_if_fail_with_msg ""
    Noi rename k to l at h che diventa ∀ p, ∃ j, P p j
  Noi rename k to l at h che diventa ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  Noi rename n to p
  Noi rename k to l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial
 -/
example (a b c : ℕ) : True := by
  Noi dimentichiamo a
  Noi dimentichiamo b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "type mismatch
  this
has type
  2 = 3 : Prop
but is expected to have type
  1 + 1 = 2 : Prop"
    Noi riformuliamo h come 2 = 3
  Noi riformuliamo h come 2 = 2
  trivial
