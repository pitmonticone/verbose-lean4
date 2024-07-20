import Verbose.Tactics.Widget
import Verbose.Italian.Help

namespace Verbose.Italian
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := en) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Noi riformuliamo $hyp come $new)

implement_endpoint (lang := en) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Dimostriamo che $new)

implement_endpoint (lang := en) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeApplied args
`(tactic|Noi concludiamo per $concl)

implement_endpoint (lang := en) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeApplied args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatEN news
`(tactic|Per $maybeApp otteniamo $newStuff)

implement_endpoint (lang := en) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Dimostriamo che $wit funziona : $goal)
| none => `(tactic|Dimostriamo che $wit funziona)

implement_endpoint (lang := en) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFacts facts
  `(tactic|Siccome $factsS concludiamo che $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Usa shift-click per selezionare sotto-espressioni."
  "Suggerimenti"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx@`(tactic| with_suggestions $seq) => do
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
    Lean.Elab.Tactic.evalTacticSeq seq
  | _ => Lean.Elab.throwUnsupportedSyntax
