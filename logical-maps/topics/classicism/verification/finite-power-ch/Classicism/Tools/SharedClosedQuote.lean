import Classicism.Tools.DeepSplitTranslate
import Classicism.Tools.CompositionalReflect
import Classicism.Tools.SharedQuoteSyntax

/-!
Quote a theorem with no metalogical type parameters using the existing native
direct quoter. Unlike `quoteStatement`, this entry point does not round-trip the
formula through elaborator syntax, which duplicates large concrete carrier types.
The generated definition and reflection theorem are both kernel checked. The
reflection uses exactly the native quoter's interpretation and rewrite lemmas.
No derivation is generated or assumed here; closed-type membership remains a
separate obligation. This command does not accept type-polymorphic statements.

OpenAI Codex, prompted by Andrew Bacon, 1 November 2026.
-/
namespace Classicism.Meta.SharedClosedQuote
open Lean Meta Elab Command Term

register_option Classicism.Meta.SharedClosedQuote.phaseFile : String := {
  defValue := ""
  descr := "Append and flush phase markers for isolated quotation/reflection checks"
}

register_option Classicism.Meta.SharedClosedQuote.splitReflection : Bool := {
  defValue := false
  descr := "Use synchronously checked compositional reflection equalities"
}

private def progress (name : Name) (phase : String) : TermElabM Unit := do
  let line := s!"{← IO.monoMsNow} shared closed quote: {name}: {phase}"
  let path := Classicism.Meta.SharedClosedQuote.phaseFile.get (← getOptions)
  if path == "" then IO.eprintln line
  else IO.FS.withFile path .append fun handle => do
    handle.putStrLn line
    handle.flush

def quoteClosed (name : Name) (quotationOnly : Bool := false) : TermElabM Unit := do
  progress name "classifying source parameters"
  let info ← getConstInfo name
  let statement ← match info with
    | .thmInfo i => pure i.type
    | .defnInfo i =>
      if i.type == mkSort .zero then pure i.value
      else throwError "shared closed quote: expected a theorem or a proposition definition"
    | _ => throwError "shared closed quote: expected a theorem or a proposition definition"
  unless info.levelParams.isEmpty do
    throwError "shared closed quote: universe parameters require the ordinary schema quoter"
  let kinds ← DeepSplitTranslate.paramKinds statement
  unless kinds.isEmpty do
    throwError "shared closed quote: type and class parameters require the ordinary schema quoter"
  progress name "quoting source statement"
  let ctx : DeepSplitTranslate.TCtx := {
    ax := mkApp (mkConst ``Classicism.Meta.C.axiomsMinus) DeepSplitTranslate.sigE
    axIsC := false }
  let (quoted, _) ←
    ((DeepSplitTranslate.withCaches (DeepSplitTranslate.quoteF statement)).run ctx).run {}
  progress name "source quotation complete; resolving metavariables"
  let quoted ← instantiateMVars quoted
  progress name "checking quotation for holes and free variables"
  if quoted.hasMVar || quoted.hasFVar || quoted.hasSorry then
    throwError "shared closed quote: quotation contains unresolved or free Lean variables"
  let sentenceTy := mkApp (mkConst ``Classicism.Meta.Sentence) DeepSplitTranslate.sigE
  let original := quoted
  progress name "sharing closed native syntax subtrees"
  let quoted ← SharedQuoteSyntax.compact (name ++ `syntaxPieces) quoted
    (fun n => progress name s!"shared syntax: {n} subtree definitions checked")
  progress name "kernel checking quotation"
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl {
      name := name ++ `quoted, levelParams := [], type := sentenceTy,
      value := quoted, hints := .abbrev, safety := .safe })
  progress name "quotation kernel check complete"
  setReducibilityStatus (name ++ `quoted) .reducible
  progress name "kernel checking literal quotation agreement"
  let agreementTy := mkApp3 (mkConst ``Eq [.succ .zero]) sentenceTy
    (mkConst (name ++ `quoted)) original
  let agreementVal := mkApp2 (mkConst ``Eq.refl [.succ .zero]) sentenceTy
    (mkConst (name ++ `quoted))
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {
      name := name ++ `quotation_agreement, levelParams := [],
      type := agreementTy, value := agreementVal })
  progress name "literal quotation agreement complete"
  if quotationOnly then return
  let interpretation := mkApp (mkConst ``Classicism.Meta.Interp.ofDomain)
    (mkConst ``Classicism.e)
  let lhs := mkApp3 (mkConst ``Classicism.Meta.Sentence.holds)
    DeepSplitTranslate.sigE interpretation (mkConst (name ++ `quoted))
  let rhs := statement
  progress name "forming reflection type"
  -- Both sides are propositions. Supply the known type explicitly instead of
  -- asking the elaborator to infer through the entire interpreted sentence.
  -- addDecl below still kernel-checks the complete equality and its proof.
  let reflectTy := mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero) lhs rhs
  progress name "reflection type constructed"
  let reflectVal ← if Classicism.Meta.SharedClosedQuote.splitReflection.get (← getOptions) then
      progress name "building checked compositional reflection equalities"
      CompositionalReflect.reflect (name ++ `reflectionPieces) lhs rhs
        (fun n => progress name s!"compositional reflection: {n} equality lemmas checked")
    else do
      -- Keep this bind inside the legacy branch. An embedded `←` in a nested
      -- conditional can otherwise run before the outer branch is selected.
      progress name "testing legacy reflection definitional equality"
      if ← isDefEq lhs rhs then
        progress name "reflection definitionally equal"
        mkEqRefl lhs
      else
        progress name "collecting reflection rewrite definitions"
        let defs ← Quote.reflectDefs rhs
        let lemmas ← (#[name ++ `quoted] ++ Quote.reflectSimpSet ++ defs).mapM fun n =>
          `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
        let stx ← `(by simp only [$lemmas,*]; try rfl)
        progress name "elaborating reflection rewrite proof"
        Term.withoutErrToSorry do
          let value ← elabTermEnsuringType stx (some reflectTy)
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars value
  progress name "reflection proof constructed; checking holes"
  if reflectVal.hasMVar || reflectVal.hasSorry then
    throwError "shared closed quote: reflection has unresolved holes"
  progress name "kernel checking reflection"
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {
      name := name ++ `reflect, levelParams := [], type := reflectTy, value := reflectVal })
  progress name "reflection complete"

/-- Continue reflection of a saved quotation, retaining only fully checked
intermediate equalities when the segment budget is reached. -/
def reflectSegment (name : Name) (budget : Nat) : TermElabM Unit := do
  let info ← getConstInfo name
  let rhs ← match info with
    | .thmInfo i => pure i.type
    | .defnInfo i => pure i.value
    | _ => throwError "reflection segment: expected source theorem or proposition definition"
  let interpretation := mkApp (mkConst ``Classicism.Meta.Interp.ofDomain)
    (mkConst ``Classicism.e)
  let lhs := mkApp3 (mkConst ``Classicism.Meta.Sentence.holds)
    DeepSplitTranslate.sigE interpretation (mkConst (name ++ `quoted))
  if (← getEnv).contains (name ++ `reflect) then
    throwError "reflection segment: reflection already completed"
  let proof? ← CompositionalReflect.reflectSegment (name ++ `reflectionPieces) lhs rhs budget
    (fun n => progress name s!"segmented reflection: {n} equality lemmas checked")
  if let some proof := proof? then
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then
      throwError "reflection segment: unresolved final proof"
    let ty := mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero) lhs rhs
    withOptions (Elab.async.set · false) do
      addDecl (.thmDecl { name := name ++ `reflect, levelParams := [], type := ty, value := proof })
    logInfo m!"{name}: segmented reflection complete ✓"

syntax (name := sharedReflectSegment) "#classicism_shared_reflect_segment " ident num : command
@[command_elab sharedReflectSegment] def elabReflectSegment : CommandElab := fun stx => do
  let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some budget := stx[2].isNatLit? | throwError "expected a segment budget"
  liftTermElabM (reflectSegment name budget)

syntax (name := sharedQuoteClosed) "#classicism_shared_quote_closed " ident+ : command

syntax (name := sharedQuotePhase) "#classicism_quote_phase " ident str : command

@[command_elab sharedQuotePhase] def elabSharedQuotePhase : CommandElab := fun stx => do
  if (← get).messages.hasErrors then
    throwError "quotation phase marker refused: an earlier command reported an error"
  let some phase := stx[2].isStrLit? | throwError "expected a phase string"
  liftTermElabM (progress stx[1].getId phase)

@[command_elab sharedQuoteClosed] def elabSharedQuoteClosed : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    liftTermElabM (quoteClosed name)
    logInfo m!"{name}: native direct quotation; reflects ✓"

end Classicism.Meta.SharedClosedQuote
