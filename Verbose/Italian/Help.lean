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
    pushCom "Se si ha già una dimostrazione {HN} di {← le.fmt} allora si può usare:"
    pushTac `(tactic|Noi concludiamo per $hyp.ident:term applicato a $HN.ident)
  else do
    pushCom "La premessa di questa implicazione è {← le.fmt}"
    pushCom "Se hai una dimostrazione {HN} di {← le.fmt}"
    pushCom "puoi usare questa ipotesi con:"
    pushTac `(tactic|Per $hyp.ident:term applicato a $HN.ident:term otteniamo $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := en) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} è un'equivalenza"
  pushCom "Si può usarlo per sostituire il lato sinistro (ovvero {← l.fmt}) con il lato destro (ovvero {← r.fmt}) nell'obiettivo con:"
  pushTac `(tactic|Noi riscriviamo usando $hyp.ident:term)
  flush
  pushCom "Si può usare per rimpiazzare il lato destro nell'obiettivo con:"
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
    pushCom "Si può usare per rimpiazzare il lato destro nell'obiettivo con:"
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
  pushTac `(tactic|(Dimostriamo una contraddizione
                    Noi concludiamo per $hypId:ident))

implement_endpoint (lang := en) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'assunzione {hyp} ensures the inclusion of {l} in {← r.fmt}."
  pushCom "Si può utilizzare con:"
  pushTac `(tactic| Per $hyp.ident:ident applicato a $x.ident usando $hx.ident otteniamo $hx'.ident:ident : $x.ident ∈ $(← r.stx))
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
  pushTac `(tactic|Noi riformuliamo $hypId:ident come $expandedHypTypeS)
  flush

implement_endpoint (lang := en) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $n₀.ident usando $hn₀.ident otteniamo $var_name'.ident:ident tale che ($ineqIdent : $ineqS) e ($hn'S : $p'S))
  pushCom "where {n₀} is {describe t} e {hn₀} is a proof of the fact that {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := en) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $n₀.ident usando $hn₀.ident otteniamo $n'.ident:ident tale che ($hn'.ident : $p'S))
  pushCom "where {n₀} is {describe t} e {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := en) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Si può utilizzare con:"
  pushTac `(tactic|Per $hyp.ident:term applicato a $n₀.ident usando $hn₀.ident otteniamo ($newsI : $pS))
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
  pushTac `(tactic|Per $hyp.ident:term applicato a $nn₀.ident e $var_name'₀.ident usando $H.ident otteniamo ($h.ident : $p'S))
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
  pushTac `(tactic|Noi applichiamo $hyp.ident:ident ad $nn₀.ident)

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
  pushCom "Non ho nulla da dire su questa ipotesi."
  flush

implement_endpoint (lang := en) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "Non ho nulla da dire su questo obiettivo."
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
  pushTac `(tactic|Dimostriamo che $expandedGoalTypeS)
  flush

implement_endpoint (lang := en) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "The next step is to announce:"
  pushTac `(tactic| Dimostriamo ora che $actualGoalS)

implement_endpoint (lang := en) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Sia $ineqS)

implement_endpoint (lang := en) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Dimostriamo che $n₀.ident works : $fullTgtS)
  pushCom "replacing {n₀} by {describe t}"

implement_endpoint (lang := en) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Dimostriamo che $nn₀.ident works : $tgt)
  pushCom "replacing {nn₀} by {describe t}"

implement_endpoint (lang := en) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... e ..."
  descrDirectProof
  pushTac `(tactic|Dimostriamo prima che $p)
  pushCom "After finish this first proof, it will remain to prove that {← p'.fmt}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Dimostriamo prima che $p')
  pushCom "then, after finishing this first proof, il will remain to prove that {← p.fmt}"

implement_endpoint (lang := en) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... or ..."
  pushCom "Hence a direct proof comincia per announcing which alternative will be proven:"
  pushTac `(tactic|Dimostriamo che $p)
  flush
  pushCom "or:"
  pushTac `(tactic|Dimostriamo che $p')

implement_endpoint (lang := en) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Assumiamo $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

implement_endpoint (lang := en) helpEquivalenceGoalSuggestion (r l : Format) (rS lS : Term) :
    SuggestionM Unit := do
  pushCom "The goal è un'equivalenza. One can announce the proof of the left to right implication with:"
  pushTac `(tactic|Dimostriamo che $lS → $rS)
  pushCom "After proving this first statement, it will remain to prove that {r} → {l}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Dimostriamo che $rS → $lS)
  pushCom "then, after finishing this first proof, il will remain to prove that {l} → {r}"

implement_endpoint (lang := en) helpSetEqSuggestion (l r : Format) (lS rS : Term) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is a set equality"
  pushCom "One can prove it by rewriting with `Noi riscriviamo usando`"
  pushCom "or start a computation usando"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "One can also prove it by double inclusion."
  pushCom "In this case the proof comincia per:"
  pushTac `(tactic|Dimostriamo prima che $lS ⊆ $rS)

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
  pushTac `(tactic|Dimostriamo prima che $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := en) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "The goal is to prove {← elem.fmt} belongs to the union of {← le.fmt} e {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Dimostriamo che $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "or by:"
  pushTac `(tactic|Dimostriamo che $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := en) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "No idea."

implement_endpoint (lang := en) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "The goal is the inclusion {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Sia $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := en) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "The goal is to prove a contradiction."
  pushCom "One can apply an assumption which is a negation"
  pushCom "namely, by definition, with shape P → false."

implement_endpoint (lang := en) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "L'obiettivo è un'implicazione."
  pushCom "Si può cominciare una dimostrazione per contrapposizione usando"
  pushTac `(tactic| Noi contrapponiamo)

implement_endpoint (lang := en) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "Si può cominciare una dimostrazione per assurdo usando"
  pushTac `(tactic| Assumiamo per assurdo $hyp:ident : $assum)

set_option linter.unusedVariables false

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Aiuto
• Per h applicato ad n₀ usando hn₀ otteniamo (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  aiuto h
  apply h
  norm_num

/--
info: Aiuto
• Per h otteniamo n tale che (n_pos : n > 0) e (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h otteniamo ε tale che (ε_pos : ε > 0) e (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a n₀ otteniamo (hn₀ : P n₀ ⇒ Q n₀)
• Noi applichiamo h ad n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  aiuto h
  exact h 2 h'

/--
info: Aiuto
• Per h applicato a n₀ otteniamo (hn₀ : P n₀)
• Noi applichiamo h to n₀
• Noi concludiamo per h applicato a 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  aiuto h
  exact h 2

/--
info: Aiuto
• Per h è sufficiente dimostrare P 1
• Noi concludiamo per h applicato a H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  aiuto h
  exact h h'

/--
info: Aiuto
• Per h applicato a H otteniamo H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h otteniamo (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Noi riscriviamo usando h
• Noi riscriviamo usando ← h
• Noi riscriviamo usando h at hyp
• Noi riscriviamo usando ← h at hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Dimostriamo prima che True
• Dimostriamo prima che 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  aiuto
  exact ⟨trivial, rfl⟩

/--
info: Aiuto
• Noi procediamo usando h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Dimostriamo che True
• Dimostriamo che False
-/
#guard_msgs in
example : True ∨ False := by
  aiuto
  left
  trivial

/-- info: Non ho nulla da dire su questa ipotesi. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• (
  Dimostriamo una contraddizione
  Noi concludiamo per h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a H otteniamo H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a k₀ usando hk₀ otteniamo n tale che (n_sup : n ≥ 3) e (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a k₀ e n₀ usando H otteniamo (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a k₀ usando hk₀ otteniamo n_1 tale che (n_1_sup : n_1 ≥ 3) e (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h otteniamo n tale che (n_sup : n ≥ 5) e (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a k₀ usando hk₀ otteniamo n tale che (n_sup : n ≥ 3) e (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h otteniamo n tale che (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a k₀ otteniamo n tale che (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h applicato a k₀ usando hk₀ otteniamo n tale che (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Dimostriamo che n₀ works: P n₀ ⇒ True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  aiuto
  use 0
  tauto

/--
info: Aiuto
• Assumiamo hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  aiuto
  exact fun _ ↦ h

/--
info: Aiuto
• Sia n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  aiuto
  intros
  trivial

/--
info: Aiuto
• Sia n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  aiuto
  exact Nat.zero_le

/--
info: Aiuto
• Dimostriamo che n₀ works: 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  aiuto
  use 1
  exact Nat.zero_le 1

/--
info: Aiuto
• Dimostriamo che n₀ works: n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  aiuto
  use 1

/-- info: Non ho nulla da dire su questa ipotesi. -/
#guard_msgs in
example (h : Odd 3) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Sia x ∈ s
---
info: Aiuto
• Per h applicato a x_1 usando hx otteniamo hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  aiuto
  Sia x ∈ s
  aiuto h
  exact h x_mem

/--
info: Aiuto
• Per h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  aiuto h
  Per h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Aiuto
• Per h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Aiuto
• Dimostriamo prima che x ∈ t
---
info: Aiuto
• Dimostriamo ora che x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  aiuto h
  Per h otteniamo (h_1 : x ∈ s) (h' : x ∈ t)
  aiuto
  Dimostriamo prima che x ∈ t
  exact h'
  aiuto
  Dimostriamo ora che x ∈ s
  exact h_1

/--
info: Aiuto
• Noi procediamo usando h
---
info: Aiuto
• Dimostriamo che x ∈ t
• Dimostriamo che x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  aiuto h
  Noi procediamo usando h
  Assumiamo hyp : x ∈ s
  aiuto
  Dimostriamo che x ∈ s
  exact hyp
  Assumiamo hyp : x ∈ t
  Dimostriamo che x ∈ t
  exact  hyp

/--
info: Aiuto
• Assumiamo hyp : False
-/
#guard_msgs in
example : False → True := by
  aiuto
  simp

/-- info: Non ho nulla da dire su questo obiettivo. -/
#guard_msgs in
example : True := by
  aiuto
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Aiuto
• Assumiamo hyp : False
• Noi contrapponiamo
-/
#guard_msgs in
example : False → True := by
  aiuto
  Noi contrapponiamo
  simp

/-- info: Non ho nulla da dire su questo obiettivo. -/
#guard_msgs in
example : True := by
  aiuto
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Aiuto
• Assumiamo per assurdo hyp : ¬True
-/
#guard_msgs in
example : True := by
  aiuto
  trivial

/--
info: Aiuto
• Per h otteniamo x_1 tale che (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  aiuto h
  trivial

/--
info: Aiuto
• Per h otteniamo x_1 tale che (x_1_dans : x_1 ∈ s) e (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  aiuto h
  trivial
