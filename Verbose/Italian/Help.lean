import Verbose.Tactics.Help
import Verbose.Tactics.Notations
import Verbose.Italian.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.Italian

open Lean.Parser.Tactic in
elab "aiuto" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "La tattica di aiuto non è abilitata."
match h with
| some h => do
    let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
    if s.isEmpty then
      logInfo (msg.getD "Nessun suggerimento")
    else
      Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Aiuto")
| none => do
    let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
    if s.isEmpty then
      logInfo (msg.getD "Nessun suggerimento")
    else
      Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Aiuto")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "un numero reale"
| "ℕ" => "un numero naturale"
| "ℤ" => "un intero"
| t => "un espressione con tipo " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "numeri reali"
| "ℕ" => "numeri naturali"
| "ℤ" => "interi"
| t => "espressioni di tipo " ++ t

def libre (s : Ident) : String :=
  s!"Il nome {s.getId} può essere scelto liberamente tra i nomi disponibili."

def printIdentList (l : List Ident) : String := commaSep <| l.toArray.map (toString ·.getId)

def libres (ls : List Ident) : String :=
s!"I nomi {printIdentList ls} possono essere scelti liberamente tra i nomi disponibili."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'assunzione {hyp} è della forma “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'assunzione {hyp} comincia per “{headDescr}”"

implement_endpoint (lang := en) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term otteniamo $nameS:ident tale che ($ineqIdent : $ineqS) e ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := en) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... e ..."
  describeHypShape hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term otteniamo ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := en) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} è della forma « ... or ... »"
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Noi procediamo usando $hyp.ident:term)

implement_endpoint (lang := en) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} è un'implicazione"
  if closes then do
    pushCom "La conclusione di questa implicazione è l'obiettivo attuale"
    pushCom "Quindi è possibile utilizzare questa ipotesi con:"
    pushTac `(tactic|Per $hyp.ident:term è sufficiente dimostrare $(← le.stx))
    flush
    pushCom "If one already has a proof {HN} of {← le.fmt} then one can use:"
    pushTac `(tactic|Noi concludiamo per $hyp.ident:term applicato a $HN.ident)
  else do
    pushCom "The premise of this implication is {← le.fmt}"
    pushCom "If you have a proof {HN} of {← le.fmt}"
    pushCom "you can use this assumption with:"
    pushTac `(tactic|Per $hyp.ident:term applicato a $HN.ident:term otteniamo $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := en) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} è un'equivalenza"
  pushCom "Si può usarlo per sostituire il lato sinistro (ovvero {← l.fmt}) con il lato destro (ovvero {← r.fmt}) nell'obiettivo con:"
  pushTac `(tactic|Noi riscriviamo usando $hyp.ident:term)
  flush
  pushCom "One can use it to replace the right-hand-side in the goal with:"
  pushTac `(tactic|Noi riscriviamo usando ← $hyp.ident)
  flush
  pushCom "One can also perform such replacements in an assumption {hyp'N} with"
  pushTac `(tactic|Noi riscriviamo usando $hyp.ident:term at $hyp'N.ident:ident)
  flush
  pushCom "or"
  pushTac `(tactic|Noi riscriviamo usando ← $hyp.ident:term at $hyp'N.ident:ident)

implement_endpoint (lang := en) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr) :
    SuggestionM Unit := do
  pushCom "L'assunzione {hyp} is an equality"
  if closes then
    pushComment <| s!"The current goal follows from it immediately"
    pushComment   "Si può utilizzare con:"
    pushTac `(tactic|Noi concludiamo per $hyp.ident:ident)
  else do
    pushCom "Si può usarlo per sostituire il lato sinistro (ovvero {← l.fmt}) con il lato destro (ovvero {← r.fmt}) nell'obiettivo con:"
    pushTac `(tactic|Noi riscriviamo usando $hyp.ident:ident)
    flush
    pushCom "One can use it to replace the right-hand-side in the goal with:"
    pushTac `(tactic|Noi riscriviamo usando ← $hyp.ident:ident)
    flush
    pushCom "One can also perform such replacements in an assumption {hyp'} with"
    pushTac `(tactic|Noi riscriviamo usando $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "or"
    pushTac `(tactic|Noi riscriviamo usando ← $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|Noi combiniamo [$hyp.ident:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities."

implement_endpoint (lang := en) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} is an inequality"
  if closes then
    flush
    pushCom "It immediately implies the current goal."
    pushCom "Si può utilizzare con:"
    pushTac `(tactic|Noi concludiamo per $hyp.ident:ident)
  else do
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|Noi combiniamo [$hyp.ident:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities or inequalities."

implement_endpoint (lang := en) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "L'assunzione {hyp} claims membership to an intersection"
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term otteniamo ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := en) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "L'assunzione {hyp} claims membership to a union"
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Noi procediamo usando $hyp.ident)

implement_endpoint (lang := en) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} is a membership"

implement_endpoint (lang := en) helpContradictiomSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "This assumption is a contradiction."
  pushCom "One can deduce anything from it with:"
  pushTac `(tactic|(Let's prove it's contradictory
                    Noi concludiamo per $hypId:ident))

implement_endpoint (lang := en) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} ensures the inclusion of {l} in {← r.fmt}."
  pushCom "Si può utilizzare con:"
  pushTac `(tactic| Per $hyp.ident:ident applicato a $x.ident using $hx.ident otteniamo $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "where {x} is {describe ambientTypePP} e {hx} proves that {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := en) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "This assumption is exactly what needs to be proven"
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Noi concludiamo per $hypId:ident)

implement_endpoint (lang := en) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "This assumption comincia per the application of a definition."
  pushCom "One can make it explicit with:"
  pushTac `(tactic|We reformulate $hypId:ident as $expandedHypTypeS)
  flush

implement_endpoint (lang := en) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $n₀.ident using $hn₀.ident otteniamo $var_name'.ident:ident tale che ($ineqIdent : $ineqS) e ($hn'S : $p'S))
  pushCom "where {n₀} is {describe t} e {hn₀} is a proof of the fact that {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := en) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $n₀.ident using $hn₀.ident otteniamo $n'.ident:ident tale che ($hn'.ident : $p'S))
  pushCom "where {n₀} is {describe t} e {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := en) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $n₀.ident using $hn₀.ident otteniamo ($newsI : $pS))
  pushCom "where {n₀} is {describe t} e {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := en) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $nn₀.ident otteniamo $var_name'.ident:ident tale che ($ineqIdent : $ineqS) e ($hn'S : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := en) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $nn₀.ident otteniamo $var_name'.ident:ident tale che ($hn'.ident : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := en) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} comincia per “{headDescr}"
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $nn₀.ident e $var_name'₀.ident using $H.ident otteniamo ($h.ident : $p'S))
  pushCom "where {nn₀} e {var_name'₀} are {describe_pl t} e {H} is a proof of {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := en) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $nn₀.ident otteniamo ($hn₀.ident : $pS))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "If this assumption won't be used again in its general shape, one can also specialize {hyp} with"
  pushTac `(tactic|We apply $hyp.ident:ident to $nn₀.ident)

implement_endpoint (lang := en) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeApplied
  pushCom "Since the goal is {but}, one can use:"
  pushTac `(tactic|Noi concludiamo per $prfS)

implement_endpoint (lang := en) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term otteniamo $n.ident:ident tale che ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := en) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"The object {hyp}" ++ match t with
    | "ℝ" => " is a fixed real number."
    | "ℕ" => " is a fixed natural number."
    | "ℤ" => " is a fixed integer."
    | s => s!" : {s} is fixed."

implement_endpoint (lang := en) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "I have nothing to say about this assumption."
  flush

implement_endpoint (lang := en) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "I have nothing to say about this goal."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal comincia per “{headDescr}”"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal è della forma “{headDescr}”"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Hence a direct proof comincia per:"

implement_endpoint (lang := en) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "The goal comincia per the application of a definition."
  pushCom "One can make it explicit with:"
  pushTac `(tactic|Let's prove that $expandedGoalTypeS)
  flush

implement_endpoint (lang := en) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "The next step is to announce:"
  pushTac `(tactic| Let's now prove that $actualGoalS)

implement_endpoint (lang := en) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Fix $ineqS)

implement_endpoint (lang := en) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Let's prove that $n₀.ident works : $fullTgtS)
  pushCom "replacing {n₀} by {describe t}"

implement_endpoint (lang := en) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Let's prove that $nn₀.ident works : $tgt)
  pushCom "replacing {nn₀} by {describe t}"

implement_endpoint (lang := en) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... e ..."
  descrDirectProof
  pushTac `(tactic|Let's first prove that $p)
  pushCom "After finish this first proof, it will remain to prove that {← p'.fmt}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Let's first prove that $p')
  pushCom "then, after finishing this first proof, il will remain to prove that {← p.fmt}"

implement_endpoint (lang := en) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... or ..."
  pushCom "Hence a direct proof comincia per announcing which alternative will be proven:"
  pushTac `(tactic|Let's prove that $p)
  flush
  pushCom "or:"
  pushTac `(tactic|Let's prove that $p')

implement_endpoint (lang := en) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Assume $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

implement_endpoint (lang := en) helpEquivalenceGoalSuggestion (r l : Format) (rS lS : Term) :
    SuggestionM Unit := do
  pushCom "The goal è un'equivalenza. One can announce the proof of the left to right implication with:"
  pushTac `(tactic|Let's prove that $lS → $rS)
  pushCom "After proving this first statement, it will remain to prove that {r} → {l}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Let's prove that $rS → $lS)
  pushCom "then, after finishing this first proof, il will remain to prove that {l} → {r}"

implement_endpoint (lang := en) helpSetEqSuggestion (l r : Format) (lS rS : Term) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is a set equality"
  pushCom "One can prove it by rewriting with `Noi riscriviamo usando`"
  pushCom "or start a computation using"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "One can also prove it by double inclusion."
  pushCom "In this case the proof comincia per:"
  pushTac `(tactic|Let's first prove that $lS ⊆ $rS)

implement_endpoint (lang := en) helpEqGoalSuggestion (l r : Format) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is an equality"
  pushCom "One can prove it by rewriting with `Noi riscriviamo usando`"
  pushCom "or start a computation using"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "Of course one can have more intermediate steps."
  pushCom "One can also make linear combination of assumptions hyp₁ hyp₂... with"
  pushCom "  Noi combiniamo [hyp₁, hyp₂]"

implement_endpoint (lang := en) helpIneqGoalSuggestion (l r : Format) (rel : String) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is an inequality"
  pushCom "One can start a computation using"
  pushCom "  calc {l}{rel}sorry := by sorry "
  pushCom "  ... = {r} := by sorry "
  pushCom "Of course one can have more intermediate steps."
  pushCom "The last computation line is not necessarily an equality, it can be an inequality."
  pushCom "Similarly the first line could be an equality. In total, the relation symbols"
  pushCom "must chain to give {rel}"
  pushCom "One can also make linear combination of assumptions hyp₁ hyp₂... with"
  pushCom "  Noi combiniamo [hyp₁, hyp₂]"

implement_endpoint (lang := en) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "The goal is prove {← elem.fmt} belongs to the intersection of {← le.fmt} with another set."
  pushCom "Hance a direct proof comincia per:"
  pushTac `(tactic|Let's first prove that $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := en) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "The goal is to prove {← elem.fmt} belongs to the union of {← le.fmt} e {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Let's prove that $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "or by:"
  pushTac `(tactic|Let's prove that $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := en) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "No idea."

implement_endpoint (lang := en) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "The goal is the inclusion {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Fix $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := en) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "The goal is to prove a contradiction."
  pushCom "One can apply an assumption which is a negation"
  pushCom "namely, by definition, with shape P → false."

implement_endpoint (lang := en) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "The goal è un'implicazione."
  pushCom "One can start a proof by contraposition using"
  pushTac `(tactic| We contrapose)

implement_endpoint (lang := en) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "One can start a proof by contradiction using"
  pushTac `(tactic| Assume for contradiction $hyp:ident : $assum)

set_option linter.unusedVariables false

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Help
• By h applicato a n₀ using hn₀ otteniamo (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  help h
  apply h
  norm_num

/--
info: Help
• By h otteniamo n tale che (n_pos : n > 0) e (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  help h
  trivial

/--
info: Help
• By h otteniamo ε tale che (ε_pos : ε > 0) e (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a n₀ otteniamo (hn₀ : P n₀ ⇒ Q n₀)
• We apply h to n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  help h
  exact h 2 h'

/--
info: Help
• By h applicato a n₀ otteniamo (hn₀ : P n₀)
• We apply h to n₀
• Noi concludiamo per h applicato a 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  help h
  exact h 2

/--
info: Help
• By h è sufficiente dimostrare P 1
• Noi concludiamo per h applicato a H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  help h
  exact h h'

/--
info: Help
• By h applicato a H otteniamo H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  help h
  trivial

/--
info: Help
• By h otteniamo (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  help h
  trivial

/--
info: Help
• Noi riscriviamo usando h
• Noi riscriviamo usando ← h
• Noi riscriviamo usando h at hyp
• Noi riscriviamo usando ← h at hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  help h
  trivial

/--
info: Help
• Let's first prove that True
• Let's first prove that 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  help
  exact ⟨trivial, rfl⟩

/--
info: Help
• Noi procediamo usando h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  help h
  trivial

/--
info: Help
• Let's prove that True
• Let's prove that False
-/
#guard_msgs in
example : True ∨ False := by
  help
  left
  trivial

/-- info: I have nothing to say about this assumption. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  help h
  trivial

/--
info: Help
• (
  Let's prove it's contradictory
  Noi concludiamo per h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  help h
  trivial

/--
info: Help
• By h applicato a H otteniamo H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a k₀ using hk₀ otteniamo n tale che (n_sup : n ≥ 3) e (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a k₀ e n₀ using H otteniamo (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a k₀ using hk₀ otteniamo n_1 tale che (n_1_sup : n_1 ≥ 3) e (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h otteniamo n tale che (n_sup : n ≥ 5) e (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a k₀ using hk₀ otteniamo n tale che (n_sup : n ≥ 3) e (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  help h
  trivial

/--
info: Help
• By h otteniamo n tale che (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a k₀ otteniamo n tale che (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
• By h applicato a k₀ using hk₀ otteniamo n tale che (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
• Let's prove that n₀ works: P n₀ ⇒ True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  help
  use 0
  tauto

/--
info: Help
• Assume hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  help
  exact fun _ ↦ h

/--
info: Help
• Fix n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  help
  intros
  trivial

/--
info: Help
• Fix n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  help
  exact Nat.zero_le

/--
info: Help
• Let's prove that n₀ works: 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  help
  use 1
  exact Nat.zero_le 1

/--
info: Help
• Let's prove that n₀ works: n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  help
  use 1

/-- info: I have nothing to say about this assumption. -/
#guard_msgs in
example (h : Odd 3) : True := by
  help h
  trivial

/--
info: Help
• Fix x ∈ s
---
info: Help
• By h applicato a x_1 using hx otteniamo hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  help
  Fix x ∈ s
  help h
  exact h x_mem

/--
info: Help
• By h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  help h
  By h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Help
• By h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Help
• Let's first prove that x ∈ t
---
info: Help
• Let's now prove that x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  help h
  By h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
  help
  Let's first prove that x ∈ t
  exact h'
  help
  Let's now prove that x ∈ s
  exact h_1

/--
info: Help
• Noi procediamo usando h
---
info: Help
• Let's prove that x ∈ t
• Let's prove that x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  help h
  Noi procediamo usando h
  Assume hyp : x ∈ s
  help
  Let's prove that x ∈ s
  exact hyp
  Assume hyp : x ∈ t
  Let's prove that x ∈ t
  exact  hyp

/--
info: Help
• Assume hyp : False
-/
#guard_msgs in
example : False → True := by
  help
  simp

/-- info: I have nothing to say about this goal. -/
#guard_msgs in
example : True := by
  help
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Help
• Assume hyp : False
• We contrapose
-/
#guard_msgs in
example : False → True := by
  help
  We contrapose
  simp

/-- info: I have nothing to say about this goal. -/
#guard_msgs in
example : True := by
  help
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Help
• Assume for contradiction hyp : ¬True
-/
#guard_msgs in
example : True := by
  help
  trivial

/--
info: Help
• By h otteniamo x_1 tale che (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  help h
  trivial

/--
info: Help
• By h otteniamo x_1 tale che (x_1_dans : x_1 ∈ s) e (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  help h
  trivial
