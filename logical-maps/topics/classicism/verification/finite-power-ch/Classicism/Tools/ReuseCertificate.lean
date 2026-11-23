import Classicism.Tools.CertificateData
import Classicism.Tools.Translate
import Classicism.Tools.GenericCompositionalQuote

/-! Reuse saved proof terms with synchronous native kernel checks, a fresh
quotation/reflection of each requested source statement, and an axiom audit.
Only theorem declarations are accepted; this command cannot add an axiom or
replace an existing declaration. No historical module is imported.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
open Lean Meta Elab Term Command
namespace Classicism.CertificateData

register_option Classicism.CertificateData.progress : String := {
  defValue := ""
  descr := "Optional append-only progress log for guarded proof-data transfer"
}

register_option Classicism.CertificateData.compositionalReflection : Bool := {
  defValue := false
  descr := "Use checked compositional reflection for ordinary Ty-parameter schemas"
}

private def reportPhase (message : String) : TermElabM Unit := do
  let path := Classicism.CertificateData.progress.get (← getOptions)
  unless path == "" do
    IO.FS.withFile path .append fun h => do h.putStrLn s!"{← IO.monoMsNow} checkpoint reuse: {message}"

private def requirePureProof (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  for ax in axs do
    unless ax == ``propext || ax == ``Quot.sound do
      throwError "reused certificate {n} has unexpected axiom {ax}"

private def importTheoremsCore (path : System.FilePath) : TermElabM Unit := do
  reportPhase s!"reading {path}"
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let format : String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| j.getObjVal? "format")
  unless format == "Classicism theorem DAG v1" do throwError "unsupported proof-data format"
  let nodes ← IO.ofExcept <| decodeNodes (← IO.ofExcept <| (← IO.ofExcept <| j.getObjVal? "nodes").getArr?)
  let decls ← IO.ofExcept <| (← IO.ofExcept <| j.getObjVal? "declarations").getArr?
  for d in decls do
    let name ← IO.ofExcept <| nameFromJson? (← IO.ofExcept <| d.getObjVal? "name")
    if (← getEnv).contains name then throwError "refusing to replace {name}"
    let levels ← IO.ofExcept <| (← IO.ofExcept <| d.getObjVal? "levelParams").getArr?
    let levelParams ← IO.ofExcept <| levels.toList.mapM nameFromJson?
    let getExpr (field : String) : TermElabM Expr := do
      let i : Nat ← IO.ofExcept <| fromJson? (← IO.ofExcept <| d.getObjVal? field)
      let some e := nodes[i]? | throwError "invalid expression reference"
      if e.hasSorry || e.hasFVar || e.hasMVar || e.hasLevelMVar then
        throwError "invalid proof term in {name}"
      return e
    let type ← getExpr "type"
    let value ← getExpr "value"
    reportPhase s!"kernel checking saved proof {name}"
    withOptions (Elab.async.set · false) do
      addDecl (.thmDecl { name, levelParams, type, value })
    requirePureProof name
    logInfo m!"saved proof kernel-checked: {name}"

def importTheorems (path : System.FilePath) : TermElabM Unit := do
  let before ← getEnv
  try
    importTheoremsCore path
  catch ex =>
    -- `addDecl` can stage a declaration before reporting its kernel error.
    -- A caller catching that error must not inherit the staged declaration.
    setEnv before
    throw ex

def checkCurrentStatement (n : Name) : TermElabM Unit := do
  reportPhase s!"quoting current statement {n}"
  let (quoted, reflectTy, reflectVal) ←
    if Classicism.CertificateData.compositionalReflection.get (← getOptions) then
      Classicism.Meta.GenericCompositionalQuote.quoteStatement n (n ++ `checkpoint140Reflection)
        (fun message => reportPhase s!"{n}: {message}")
    else
      Classicism.Meta.Quote.quoteStatement (← getConstInfo n).type
  reportPhase s!"checking current reflection {n}"
  Classicism.Meta.Quote.declareQuoted n quoted reflectTy reflectVal
  let reused := n ++ `derivable
  let (expected, value) ← lambdaTelescope quoted fun xs sentence => do
    let sig := Lean.mkConst ``Classicism.Meta.Signature.pure
    let ax := mkApp (Lean.mkConst ``Classicism.Meta.C.axiomsMinus) sig
    let proof := mkAppN (Lean.mkConst reused) xs
    let got := (← inferType proof).getAppArgs.back!
    -- The historical translator and the source quoter can differ by object
    -- beta/eta conversion. Reuse the native conversion prover; the kernel
    -- checks the resulting derivation against the *fresh* quoted statement.
    let ctx : Classicism.Meta.Translate.TCtx := { ax, axIsC := false }
    reportPhase s!"constructing beta/eta conversion {n}"
    let (converted, _) ← ((Classicism.Meta.Translate.withCaches
      (Classicism.Meta.Translate.coerce proof got sentence)).run ctx).run {}
    let expected ← mkForallFVars xs (mkAppN (Lean.mkConst ``Classicism.Meta.Theorem) #[sig, ax, sentence])
    pure (expected, ← mkLambdaFVars xs converted)
  let checked := n ++ `checkpoint140_exact
  reportPhase s!"kernel checking exact-statement bridge {n}"
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := checked, levelParams := [], type := expected, value })
  requirePureProof checked
  reportPhase s!"current statement and axiom audit complete {n}"
  logInfo m!"checkpoint 140 proves current quotation in C⁻: {n}"

syntax (name := reuseCheckpoint) "#classicism_reuse_checkpoint " str ident+ : command
@[command_elab reuseCheckpoint] def elabReuseCheckpoint : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwError "expected a proof-data path"
  let before ← getEnv
  try
    liftTermElabM (importTheorems path)
    for id in stx[2].getArgs do
      let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
      liftTermElabM (checkCurrentStatement n)
  catch ex =>
    setEnv before
    throw ex

end Classicism.CertificateData
