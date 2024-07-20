import Verbose.Tactics.Common

open Lean

namespace Verbose.Italian

declare_syntax_cat appliedTo
syntax "applicato a " sepBy(term, "e") : appliedTo

def appliedToTerm : TSyntax `appliedTo → Array Term
| `(appliedTo| applicato a $[$args]e*) => args
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat usingStuff
syntax " utilizzando " sepBy(term, "e") : usingStuff
syntax " utilizzando che " term : usingStuff

def usingStuffToTerm : TSyntax `usingStuff → Array Term
| `(usingStuff| utilizzando $[$args]e*) => args
| `(usingStuff| utilizzando che $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat maybeApplied
syntax term (appliedTo)? (usingStuff)? : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $expr:term) => pure expr
| `(maybeApplied| $expr:term $args:appliedTo) => `($expr $(appliedToTerm args)*)
| `(maybeApplied| $expr:term $args:usingStuff) => `($expr $(usingStuffToTerm args)*)
| `(maybeApplied| $expr:term $args:appliedTo $extras:usingStuff) =>
  `($expr $(appliedToTerm args)* $(usingStuffToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeApplied

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeApplied)
| [x] => `(maybeApplied|$x:term)
| [x, y] => `(maybeApplied|$x:term applicato a $y)
| [x, y, z] => `(maybeApplied|$x:term applicato a $y utilizzando che $z)
| x::y::l => `(maybeApplied|$x:term applicato a $y:term utilizzando [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuff
syntax (ppSpace colGt maybeTypedIdent)* : newStuff
syntax maybeTypedIdent "tale che" ppSpace colGt maybeTypedIdent : newStuff
syntax maybeTypedIdent "tale che" ppSpace colGt maybeTypedIdent " e "
       ppSpace colGt maybeTypedIdent : newStuff

def newStuffToArray : TSyntax `newStuff → Array MaybeTypedIdent
| `(newStuff| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuff| $x:maybeTypedIdent tale che $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuff| $x:maybeTypedIdent tale che $y:maybeTypedIdent e $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatEN : List MaybeTypedIdent → MetaM (TSyntax `newStuff)
| [x] => do `(newStuff| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuff| $(← x.stx):maybeTypedIdent tale che $(← y.stx'))
| [x, y, z] => do `(newStuff| $(← x.stx):maybeTypedIdent tale che $(← y.stx) e $(← z.stx))
| _ => pure default

declare_syntax_cat newFacts
syntax colGt namedType : newFacts
syntax colGt namedType " e "  colGt namedType : newFacts
syntax colGt namedType ", "  colGt namedType " e "  colGt namedType : newFacts

def newFactsToArray : TSyntax `newFacts → Array NamedType
| `(newFacts| $x:namedType) => #[toNamedType x]
| `(newFacts| $x:namedType e $y:namedType) =>
    #[toNamedType x, toNamedType y]
| `(newFacts| $x:namedType, $y:namedType e $z:namedType) =>
    #[toNamedType x, toNamedType y, toNamedType z]
| _ => #[]

def newFactsToTypeTerm : TSyntax `newFacts → MetaM Term
| `(newFacts| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFacts| $x:namedType e $y) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    `($xT ∧ $yT)
| `(newFacts| $x:namedType, $y:namedType e $z) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $yT ∧ $zT)
| _ => throwError "Impossibile convertire la descrizione dei nuovi fatti in un termine."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsToRCasesPatt : TSyntax `newFacts → RCasesPatt
| `(newFacts| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFacts| $x:namedType e $y:namedType) => namedTypeListToRCasesPatt [x, y]
| `(newFacts|  $x:namedType, $y:namedType e $z:namedType) => namedTypeListToRCasesPatt [x, y, z]
| _ => default

declare_syntax_cat newObject
syntax maybeTypedIdent "tale che" maybeTypedIdent : newObject
syntax maybeTypedIdent "tale che" maybeTypedIdent colGt " e " maybeTypedIdent : newObject

def newObjectToTerm : TSyntax `newObject → MetaM Term
| `(newObject| $x:maybeTypedIdent tale che $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObject| $x:maybeTypedIdent tale che $new₁ e $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "Impossibile convertire il nuovo oggetto in un termine."

-- TODO: create helper functions for the values below
open Tactic Lean.Elab.Tactic.RCases in
def newObjectToRCasesPatt : TSyntax `newObject → RCasesPatt
| `(newObject| $x:maybeTypedIdent tale che $new) => maybeTypedIdentListToRCasesPatt [x, new]
| `(newObject| $x:maybeTypedIdent tale che $new₁ e $new₂) => maybeTypedIdentListToRCasesPatt [x, new₁, new₂]
| _ => default

declare_syntax_cat facts
syntax term : facts
syntax term " e " term : facts
syntax term ", " term " e " term : facts

def factsToArray : TSyntax `facts → Array Term
| `(facts| $x:term) => #[x]
| `(facts| $x:term e $y:term) => #[x, y]
| `(facts| $x:term, $y:term e $z:term) => #[x, y, z]
| _ => #[]

def arrayToFacts : Array Term → CoreM (TSyntax `facts)
| #[x] => `(facts| $x:term)
| #[x, y] => `(facts| $x:term e $y:term)
| #[x, y, z] => `(facts| $x:term, $y:term e $z:term)
| _ => default

end Verbose.Italian

/-- Convert an expression to a `maybeApplied` syntax object, in `MetaM`. -/
def Lean.Expr.toMaybeApplied (expr : Expr) : MetaM (TSyntax `maybeApplied) := do
  let fn := expr.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match expr.getAppArgs.toList with
  | [] => `(maybeApplied|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeApplied|$fnS:term applicato a $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeApplied|$fnS:term applicato a [$arr:term,*])

implement_endpoint (lang := en) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"Il nome {n} è già utilizzato."

implement_endpoint (lang := en) notDefEq (expr val : MessageData) : CoreM MessageData :=
pure m!"Il termine fornito{expr}\nnon è uguale per definizione a quello atteso{val}"

implement_endpoint (lang := en) notAppConst : CoreM String :=
pure "Non è l'applicazione di una definizione."

implement_endpoint (lang := en) cannotExpand : CoreM String :=
pure "Impossibile espandere la definizione del simbolo della testa."

implement_endpoint (lang := en) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"L'affermazione {tgt} non sembra derivare direttamente da al più un'ipotesi locale."
