import Classicism.Certified.MathematicalContingency.EndpointAssembly37Segment224
import Classicism.Certified.MathematicalContingency.EndpointAssembly37ConversionRepair
import Classicism.Tools.BoundAssembly37

/-! Bounded, kernel-checked conversion continuation. Partial segments do not
assert the target. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Classicism.Meta.BoundAssembly37.repairEnclosing true
set_option Classicism.Meta.BoundAssembly37.reuseSubtrees true
set_option Classicism.Meta.BoundAssembly37.directBeta true
set_option Classicism.Meta.BoundAssembly37.profile true
set_option Classicism.Meta.BoundAssembly37.progress ".lake/finite-power-endpoint-progress.log"
set_option Classicism.Meta.BoundAssembly37.conversionTrace ".lake/finite-power-assembly37-segment225.log"
set_option Classicism.Meta.ConversionCache.progress ".lake/finite-power-assembly37-cache-segment225.log"
open Lean Meta Elab Term Command Classicism.Meta.Quote
namespace Classicism.Meta.BoundAssembly37
partial def translateSharedFinal (c : Name) (ls : List Level) (name : Name) : TrM Unit := do
  let keyS := name.toString
  let saved ← get
  if (← get).specs.contains keyS then
    throwError "derive: {c} depends on itself"
  modify fun s => { s with specs := s.specs.insert keyS }
  trace s!"  translating {c} ({(← get).specs.size} in progress)"
  let info ← getConstInfo c
  let .thmInfo _ := info | throwError "derive: {c} is not a theorem"
  let ty := info.type.instantiateLevelParams info.levelParams ls
  let value := (info.value! (allowOpaque := true)).instantiateLevelParams info.levelParams ls
  let kinds ← paramKinds ty
  let k := kinds.size
  let ax := (← read).ax
  let (dty, dval) ← forallTelescope ty fun xs body => do
    let stmt ← mkForallFVars (xs.extract k xs.size) body
    let val := (value.beta (xs.extract 0 k)).headBeta
    let rec go (i : Nat) (tyVars : List (FVarId × Kind × Expr)) (tvs : Array Expr) : TrM (Expr × Expr) := do
      if h : i < k then
        match kinds[i] with
        | none => go (i + 1) tyVars tvs
        | some kind =>
          let x := xs[i]!
          let tyOfKind := if kind == .ty then tyE else Lean.mkConst ``Classicism.Meta.RTy
          withLocalDeclD ((← x.fvarId!.getUserName).appendAfter "'") tyOfKind fun tv =>
            go (i + 1) ((x.fvarId!, kind, tv) :: tyVars) (tvs.push tv)
      else
        withReader (fun c => { c with q := { tyVars := tyVars }, hyps := [], ihs := [], logicalDepth := 0 }) <| withCaches do
          let S ← quoteF stmt
          let (got, d) ← interp val
          conversionPhase "generic-interpreted"
          let d ← coerce d got S
          conversionPhase "generic-coerced"
          let thmTy := mkAppN (mkConst ``Classicism.Meta.Theorem) #[sigE, ax, S]
          conversionPhase "generic-abstract-type-BEGIN"
          let dty ← mkForallFVars tvs thmTy
          conversionPhase "generic-abstract-proof-BEGIN"
          let dval ← mkLambdaFVars tvs d
          conversionPhase "generic-abstract-proof-END"
          return (dty, dval)
    go 0 [] #[]
  modify fun s => { s with specs := s.specs.erase keyS }
  restoreMemo saved
  let (dty, dval) := ShareCommon.shareCommon' (dty, dval)
  let t₀ ← IO.monoMsNow
  conversionPhase "generic-kernel-BEGIN"
  timed "addDecl" (withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := dty, value := dval }))
  conversionPhase "generic-kernel-END"
  trace s!"  ✓ {c}: kernel {(← IO.monoMsNow) - t₀} ms, depth {dval.approxDepth}"
  modify fun s => { s with timing := s.timing.insert "translations" (s.timing.getD "translations" 0 + 1) }
  restoreMemo saved

def deriveSharedFinal (foo : Name) : TermElabM Unit := do
  let info ← getConstInfo foo
  let .thmInfo _ := info | throwError "derive: {foo} is not a theorem"
  let axs ← collectAxioms foo
  let axIsC := axs.contains ``Classicism.e_exists
  let ax := mkApp (mkConst (if axIsC then ``Classicism.Meta.C.axioms else ``Classicism.Meta.C.axiomsMinus)) sigE
  let tctx : TCtx := { ax := ax, axIsC := axIsC }
  let ((), st) ← (translateSharedFinal foo [] (foo ++ `derivable)).run tctx |>.run {}
  if Classicism.Meta.BoundAssembly37.profile.get (← getOptions) then
    logInfo m!"profile (ms): {st.timing.toList}"

end Classicism.Meta.BoundAssembly37
namespace Classicism.Meta.StagedBound37
syntax (name := stagedSharedFinal) "#classicism_staged_shared_final " ident num : command
@[command_elab stagedSharedFinal] def elabStagedSharedFinal : CommandElab := fun stx => do
  let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some budget := stx[2].isNatLit? | throwError "expected conversion budget"
  let before ← getEnv
  ConversionCache.exported.set 0
  ConversionCache.reused.set 0
  try
    unless (← getEnv).contains (name ++ `derivable) do
      withScope (fun scope => { scope with opts := (ConversionCache.prefix.set
          (ConversionCache.budget.set scope.opts budget) name.toString) }) do
        liftTermElabM (BoundAssembly37.deriveSharedFinal name)
    liftCoreM (ConversionCache.requirePure (name ++ `derivable))
    logInfo m!"staged derivation complete: {name}; new auxiliaries {← ConversionCache.exported.get}; reused {← ConversionCache.reused.get}"
  catch ex =>
    match ex with
    | .internal id _ =>
      if id == ConversionCache.budgetExceeded then
        if (← getEnv).contains (name ++ `derivable) then
          setEnv before
          throwError "staged derivation: final declaration appeared during an incomplete segment"
        logInfo m!"staged derivation incomplete: {name}; new auxiliaries {← ConversionCache.exported.get}; reused {← ConversionCache.reused.get}"
      else
        setEnv before
        throw ex
    | _ =>
      setEnv before
      throw ex

end Classicism.Meta.StagedBound37

#classicism_staged_shared_final Classicism.MathematicalContingency.FinitePower.negative_possible_not_cardinalCH 1
run_cmd do
  IO.FS.withFile ".lake/finite-power-quotation-phases.log" .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} bounded conversion segment complete; awaiting export"
