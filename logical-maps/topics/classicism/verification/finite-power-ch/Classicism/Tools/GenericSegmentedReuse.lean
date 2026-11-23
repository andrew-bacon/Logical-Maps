import Classicism.Tools.ReuseCertificate

/-! Resumable native quotation/reflection for schemas whose
metalogical parameters are ordinary `Ty` parameters. Type parameters remain
external to object quantification. RelTy/Rel/Order/Pointwise parameters are
rejected explicitly; use the general native quoter for those schemas.
The quotation plumbing follows GenericCompositionalQuote; the existing
CompositionalReflect.reflectSegment exports bounded, kernel-checked pieces.
The final segment converts a previously checked saved object proof to this
fresh quotation. Partial segments supply no final reflection or derivation.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
open Lean Meta Elab Term
namespace Classicism.Meta.GenericSegmentedReuse

def quoteStatementSegment (name declPrefix : Name) (budget : Nat)
    (phase : String → TermElabM Unit := fun _ => pure ()) : TermElabM (Expr × Expr × Option Expr) := do
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do throwError "generic reflection: universe parameters unsupported"
  let ty := info.type
  forallTelescope ty fun xs body => do
    let mut k := 0
    let mut types : Array Expr := #[]
    for x in xs do
      let t ← whnf (← inferType x)
      if t.isSort && !t.isProp then
        types := types.push x
        k := k + 1
      else if let some cls ← isClass? t then
        unless cls == ``Classicism.Ty do
          throwError "generic reflection: unsupported marker class {cls}"
        k := k + 1
      else break
    let statement ← mkForallFVars (xs.extract k xs.size) body
    let rec go (i : Nat) (qctx : Quote.QCtx) (tvs : Array Expr) : TermElabM (Expr × Expr × Option Expr) := do
      if h : i < types.size then
        let x := types[i]
        withLocalDeclD ((← x.fvarId!.getUserName).appendAfter "'") (Lean.mkConst ``Classicism.Meta.Ty) fun tv =>
          go (i + 1) { qctx with tyVars := (x.fvarId!, .ty, tv) :: qctx.tyVars } (tvs.push tv)
      else
        phase "direct quotation under generic object-type parameters"
        let sig := DeepSplitTranslate.sigE
        let ctx : DeepSplitTranslate.TCtx := {
          q := qctx, ax := mkApp (Lean.mkConst ``Classicism.Meta.C.axiomsMinus) sig, axIsC := false }
        let (quoted, _) ← ((DeepSplitTranslate.withCaches
          (DeepSplitTranslate.quoteF statement)).run ctx).run {}
        let quoted ← instantiateMVars quoted
        if quoted.hasMVar || quoted.hasSorry then throwError "generic quotation has unresolved holes"
        let domain := Lean.mkConst ``Classicism.e
        let interpretation := mkApp (Lean.mkConst ``Classicism.Meta.Interp.ofDomain) domain
        let lhs := mkApp3 (Lean.mkConst ``Classicism.Meta.Sentence.holds) sig interpretation quoted
        let mut rhs := ty
        let mut ti := 0
        for _ in [0:k] do
          let .forallE _ d b _ := rhs | throwError "generic reflection: malformed telescope"
          let d ← whnf d
          let arg ← if d.isSort then do
              let tv := tvs[ti]!
              ti := ti + 1
              pure (mkApp2 (Lean.mkConst ``Classicism.Meta.Ty.denote) domain tv)
            else do
              unless d.getAppFn.isConstOf ``Classicism.Ty do
                throwError "generic reflection: expected Ty marker"
              pure (mkApp2 (Lean.mkConst ``Classicism.Ty.mk) d.getAppArgs[0]! (Lean.mkConst ``Unit.unit))
          rhs := b.instantiate1 arg
        phase "checking compositional reflection equalities"
        let proof ← CompositionalReflect.reflectSegment declPrefix lhs rhs budget
          (fun n => phase s!"{n} reflection equalities checked")
        let eq := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (mkSort .zero) lhs rhs
        let proof ← proof.mapM (fun p => mkLambdaFVars tvs p)
        pure (← mkLambdaFVars tvs quoted, ← mkForallFVars tvs eq, proof)
    go 0 {} #[]



private def requirePure (n : Name) : CoreM Unit := do
  for ax in (← collectAxioms n) do
    unless ax == ``propext || ax == ``Quot.sound do
      throwError "generic segmented reuse: unexpected object-proof axiom {ax}"

/-- Convert a saved proof to the freshly quoted statement; no axiom is added. -/
def bridge (source checked : Name) (quoted : Expr) : TermElabM Unit := do
  let before ← getEnv
  try
    let (expected, value) ← lambdaTelescope quoted fun xs sentence => do
      let sig := Lean.mkConst ``Classicism.Meta.Signature.pure
      let ax := mkApp (Lean.mkConst ``Classicism.Meta.C.axiomsMinus) sig
      let proof := mkAppN (Lean.mkConst (source ++ `derivable)) xs
      let got := (← inferType proof).getAppArgs.back!
      let ctx : Classicism.Meta.Translate.TCtx := { ax, axIsC := false }
      let (converted, _) ← ((Classicism.Meta.Translate.withCaches
        (Classicism.Meta.Translate.coerce proof got sentence)).run ctx).run {}
      pure (← mkForallFVars xs (mkAppN (Lean.mkConst ``Classicism.Meta.Theorem) #[sig, ax, sentence]),
            ← mkLambdaFVars xs converted)
    withOptions (Elab.async.set · false) do
      addDecl (.thmDecl { name := checked, levelParams := [], type := expected, value })
    requirePure checked
  catch ex =>
    setEnv before
    throw ex

private def reportPhase (message : String) : TermElabM Unit := do
  let path := (← getOptions).get `Classicism.CertificateData.progress ""
  unless path == "" do
    IO.FS.withFile path .append fun h => do
      h.putStrLn s!"{← IO.monoMsNow} generic segmented reuse: {message}"

open Lean.Elab.Command
syntax (name := genericReuseSegment) "#classicism_generic_reuse_segment " ident num : command
@[command_elab genericReuseSegment] def elabGenericReuseSegment : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some budget := stx[2].isNatLit? | throwError "expected reflection budget"
  let before ← getEnv
  try
    liftTermElabM do
      let (q, ty, proof) ← quoteStatementSegment n (n ++ `checkpoint140Reflection) budget reportPhase
      if let some value := proof then
        Classicism.Meta.Quote.declareQuoted n q ty value
        bridge n (n ++ `checkpoint140_exact) q
        reportPhase s!"current statement and axiom audit complete {n}"
        logInfo m!"checkpoint 140 proves current quotation in C⁻: {n}"
      else
        reportPhase s!"reflection incomplete {n}"
        logInfo m!"generic reuse segment incomplete: {n}"
  catch ex =>
    setEnv before
    throw ex

end Classicism.Meta.GenericSegmentedReuse
