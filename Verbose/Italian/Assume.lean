import Verbose.Italian.Fix

open Lean Elab Tactic

syntax "Assumiamo₁ " colGt assumeDecl : tactic
syntax "Assumiamo " "che"? (colGt assumeDecl)+ : tactic
syntax "Assumiamo " "per assurdo " (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Assumiamo₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Assumiamo₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Assumiamo₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Assumiamo₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Assumiamo $[che]? $decl:assumeDecl) => `(tactic| Assumiamo₁ $decl)
  | `(tactic| Assumiamo $[che]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Assumiamo₁ $decl; Assumiamo $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Assumiamo per assurdo $x:ident : $type) => forContradiction x.getId type

example (P Q : Prop) : P → Q → True := by
  Assumiamo hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Assumiamo che hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Assumiamo che hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "Non c'è alcuna ipotesi da introdurre qui."
    Assumiamo n
  intro n
  Assumiamo H : n > 0
  trivial

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assumiamo hP
  Assumiamo per assurdo hnQ :¬ Q
  exact h hnQ hP

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assumiamo hP
  Assumiamo per assurdo hnQ : ¬ Q
  exact h hnQ hP

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "L'obiettivo è già una negazione, dimostrarlo per assurdo non porta a nulla. Puoi assumere direttamente 0 = 1."
    Assumiamo per assurdo h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Assumiamo h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Assumiamo per assurdo h : 0 = 1
  norm_num at h
