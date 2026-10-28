import Classicism.MathematicalContingency.Certificates.DoubleHartogsPieces01
import Classicism.MathematicalContingency.Certificates.DoubleHartogsPieces02
import Classicism.MathematicalContingency.Certificates.CommonPairedBound02
import Classicism.MathematicalContingency.HartogsCommonBound
import Lean
open Lean Meta Elab Term
open Classicism.Meta.Translate
set_option maxHeartbeats 0
set_option maxRecDepth 20000

partial def exprMetrics (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get)[e]? then return n
  let children := match e with
    | .app f a => [f,a]
    | .lam _ t b _ | .forallE _ t b _ => [t,b]
    | .letE _ t v b _ => [t,v,b]
    | .mdata _ b | .proj _ _ b => [b]
    | _ => []
  let mut n := 1
  for c in children do n := min 1000000000000 (n + (← exprMetrics c))
  modify (·.insert e n)
  return n

def emitMetric (label : String) (e : Expr) : TermElabM Unit := do
  let (tree,memo) := (exprMetrics e).run {}
  let msg := s!"{label}: dag={memo.size}, tree_capped={tree}, depth={e.approxDepth}"
  IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-growth.trace" .append (fun h => h.putStrLn msg)

partial def probeQuote (c : Name) : TermElabM Unit := do
  let info ← getConstInfo c
  emitMetric s!"{c} shallow_type" info.type
  emitMetric s!"{c} shallow_proof" (info.value! (allowOpaque := true))
  let kinds ← paramKinds info.type
  let k := kinds.size
  let ax := mkApp (mkConst ``Classicism.Meta.C.axiomsMinus) sigE
  let action : TrM Unit := forallTelescope info.type fun xs body => do
    let stmt ← mkForallFVars (xs.extract k xs.size) body
    let rec go (i : Nat) (tyVars : List (FVarId × Classicism.Meta.Quote.Kind × Expr)) : TrM Unit := do
      if h : i < k then
        match kinds[i] with
        | none => go (i+1) tyVars
        | some kind =>
          let t := if kind == .ty then tyE else mkConst ``Classicism.Meta.RTy
          withLocalDeclD `T t fun tv => go (i+1) ((xs[i]!.fvarId!,kind,tv)::tyVars)
      else
        withReader (fun ctx => {ctx with q := {tyVars := tyVars}, hyps := []}) <| withCaches do
          let start ← IO.monoMsNow
          let q ← quoteF stmt
          emitMetric s!"{c} quotation ms={(← IO.monoMsNow)-start}" q
    go 0 []
  let _ ← (action.run {ax:=ax,axIsC:=false}).run {}
  if let some cert := (← getEnv).find? (c ++ `derivable) then
    emitMetric s!"{c} certificate_type" cert.type
    emitMetric s!"{c} certificate_proof" (cert.value! (allowOpaque := true))

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Classicism.MathematicalContingency.commonPairedBound_of_nontrivial,
    ``Classicism.MathematicalContingency.doubleHartogs_embeds_base,
    ``Classicism.MathematicalContingency.doubleHartogs_pairing_closed,
    ``Classicism.MathematicalContingency.doubleHartogs_commonPairedBound_nontrivial] do
    probeQuote n
