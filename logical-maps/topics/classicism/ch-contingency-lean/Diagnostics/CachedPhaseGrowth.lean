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

structure ConversionCache where
  terms : Std.HashMap (Expr × Tm) Expr := {}
  diffs : Std.HashMap (Expr × Tm × Tm) (Option Expr) := {}

partial def cachedToTerm (memo : IO.Ref ConversionCache) (Γ : Expr) (tm : Tm) : TrM Expr := do
  if let some r := (← memo.get).terms[(Γ,tm)]? then return r
  let r ← go tm
  memo.modify fun s => {s with terms := s.terms.insert (Γ,tm) r}
  return r
where
  go : Tm → TrM Expr
  | .var i => do
    modify fun s => { s with timing := s.timing.insert "toTerm.var" (s.timing.getD "toTerm.var" 0 + 1) }
    let (v, σ) := varIn Γ i
    return mkTVar Γ σ v
  | .app σ ρ f a => return mkTApp Γ σ ρ (← cachedToTerm memo Γ f) (← cachedToTerm memo Γ a)
  | .lam σ ρ b => return mkTLam Γ σ ρ (← cachedToTerm memo (mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, Γ]) b)
  | .const n ty => return constIn Γ n ty
  | .opaque Γ' e => do
    unless Γ' == Γ do
      throwError "derive: an unreadable subterm{indentExpr e}\nmoved under a binder by a conversion"
    return e

partial def cachedDiffConv (memo : IO.Ref ConversionCache) (Γ : Expr) (g e : Tm) (level : Nat := 0) : TrM (Option Expr) := do
  let mark (msg : String) : TrM Unit := do
    if level < 2 then IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-cache-phases.trace" .append (fun h => h.putStrLn s!"level={level} {msg}")
  mark "equality"
  if g == e then return none
  mark "cache lookup"
  if let some r := (← memo.get).diffs[(Γ,g,e)]? then return r
  mark "recursive construction"
  let r ← go
  mark "cache insert"
  memo.modify fun s => {s with diffs := s.diffs.insert (Γ,g,e) r}
  return r
where
  stable (label : String) (t : Tm) : TrM Bool := do
    if level < 2 then IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-cache-phases.trace" .append (fun h => h.putStrLn s!"level={level} rootStable {label} BEGIN")
    let r ← rootStable t
    if level < 2 then IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-cache-phases.trace" .append (fun h => h.putStrLn s!"level={level} rootStable {label} END")
    return r
  go : TrM (Option Expr) := do
    match g, e with
    | .app σ ρ f a, .app σ' ρ' f' a' =>
      if σ == σ' && ρ == ρ' && (← stable "got" g) && (← stable "expected" e) then
        let pf ← cachedDiffConv memo Γ f f' (level+1)
        let pa ← cachedDiffConv memo Γ a a' (level+1)
        if pf.isNone && pa.isNone then return none
        let fE ← cachedToTerm memo Γ f; let aE ← cachedToTerm memo Γ a
        let pf := pf.getD (convRefl Γ (tRel (tArr σ ρ)) fE)
        let pa := pa.getD (convRefl Γ σ aE)
        return some (mkAppN (mkConst ``Classicism.Meta.Conv.app_congr)
          #[sigE, Γ, σ, ρ, fE, ← cachedToTerm memo Γ f', aE, ← cachedToTerm memo Γ a', pf, pa])
      else byNf
    | .lam σ ρ b, .lam σ' ρ' b' =>
      if σ == σ' && ρ == ρ' && (← stable "got" g) && (← stable "expected" e) then
        let Γ' := mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, Γ]
        let some pb ← cachedDiffConv memo Γ' b b' (level+1) | return none
        return some (mkAppN (mkConst ``Classicism.Meta.Conv.lam_congr)
          #[sigE, Γ, σ, ρ, ← cachedToTerm memo Γ' b, ← cachedToTerm memo Γ' b', pb])
      else byNf
    | _, _ => byNf
  byNf : TrM (Option Expr) := do
    let (gn, kg) ← normalizeTm g
    let (en, ke) ← normalizeTm e
    unless gn == en do
      throwError "derive: internal error, subterms that do not convert: {repr g} and {repr e}"
    let T ← typeOf Γ g
    let gE ← cachedToTerm memo Γ g; let eE ← cachedToTerm memo Γ e
    let termTy := mkApp3 (mkConst ``Classicism.Meta.Term) sigE Γ T
    let refl (t : Expr) : Expr := mkAppN (mkConst ``Eq.refl [Level.one]) #[termTy, t]
    let kind := s!"conv[{max kg ke} passes]"
    modify fun s => { s with timing := s.timing.insert kind (s.timing.getD kind 0 + 1) }
    -- always one-sided: the kernel evaluates the normalizer on one side against a tree
    -- as written. Given `nf n a = nf n b` it would instead unfold both sides in step,
    -- comparing the recursor's minor premises at every level.
    if ke == 0 then
      return some (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_left) #[sigE, Γ, T, mkRawNatLit kg, gE, eE, refl eE])
    else if kg == 0 then
      return some (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_right) #[sigE, Γ, T, mkRawNatLit ke, gE, eE, refl gE])
    else
      let N ← cachedToTerm memo Γ gn
      let p₁ := mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_left) #[sigE, Γ, T, mkRawNatLit kg, gE, N, refl N]
      let p₂ := mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_right) #[sigE, Γ, T, mkRawNatLit ke, N, eE, refl N]
      return some (convTrans Γ T gE N eE p₁ p₂)

def cachedCanon (memo : IO.Ref ConversionCache) (t : Expr) : TrM (Expr × Option Expr) := do
  let Γ ← ctxE
  let T ← cachedToTerm memo Γ (← shadow t)
  if T == t then return (T, none)
  let termTy := mkApp3 (mkConst ``Classicism.Meta.Term) sigE Γ tyT
  let h := mkAppN (mkConst ``Eq.refl [Level.one]) #[termTy, T]
  return (T, some (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_left) #[sigE, Γ, tyT, mkRawNatLit 0, t, T, h]))

def tracedCoerce (memo : IO.Ref ConversionCache) (d got exp : Expr) : TrM Expr := do
  let say (msg : String) : TrM Unit := IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-cached-phased-feed.trace" .append (fun h => h.putStrLn msg)
  let got ← instantiateMVars got
  let exp ← instantiateMVars exp
  if got == exp then return d
  say "coerce phase shadowNf got"
  let (g', _) ← shadowNf got
  say "coerce phase shadowNf expected"
  let (e', _) ← shadowNf exp
  unless g' == e' do
    throwError "derive: the derivation proves{indentExpr got}\nbut{indentExpr exp}\nwas expected, and the two do not convert; normal forms {repr g'} and {repr e'}"
  let Γ ← ctxE
  say "coerce phase canon got"
  let (gT, bg) ← cachedCanon memo got
  say "coerce phase canon expected"
  let (eT, be) ← cachedCanon memo exp
  -- between the two trees: the local certificate, `of_nf` only where they differ
  say "coerce phase diffConv"
  let mid ← timed "diff" (cachedDiffConv memo Γ (← shadow got) (← shadow exp))
  if mid.isNone then
    modify fun s => { s with timing := s.timing.insert "defeq" (s.timing.getD "defeq" 0 + 1) }
  say "coerce phase assemble conversion"
  let c ← if Classicism.Meta.Translate.convAxiom.get (← getOptions) then
      pure (mkApp2 (mkConst ``sorryAx [Level.zero]) (mkAppN (mkConst ``Classicism.Meta.Conv) #[sigE, Γ, tyT, got, exp]) (mkConst ``Bool.false))
    else
      -- `got ≡ gT ≡ eT ≡ exp`, each link present only where needed
      let mut c : Option (Expr × Expr) := none   -- a proof of `got ≡ x`, with `x`
      if let some bg := bg then c := some (bg, gT)
      if let some m := mid then
        c := some (match c with
          | none => (m, eT)
          | some (p, _) => (convTrans Γ tyT got gT eT p m, eT))
      if let some be := be then
        let be' := convSymm Γ tyT exp eT be
        c := some (match c with
          | none => (be', exp)
          | some (p, x) => (convTrans Γ tyT got x exp p be', exp))
      match c with
      | some (p, _) => pure p
      | none => pure (convRefl Γ tyT got)
  say "coerce phase conversion rule"
  rule ``Classicism.Meta.Derivable.conv #[Γ, ← hypsE, got, exp, d, c]

-- Diagnostic copy of feed's object branch, with phase markers only.
def tracedObjectFeed (cur F d a : Expr) : TrM (Expr × Expr) := do
  let say (msg : String) : TrM Unit := IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-cached-phased-feed.trace" .append (fun h => h.putStrLn msg)
  let Γ ← ctxE
  let Δ ← hypsE
  let .forallE nm dom body _ ← whnf (← inferType cur) | throwError "expected forall"
  let body := betaDeep body
  say "phase quote domain"
  let σ ← (Classicism.Meta.Quote.quoteTy dom).run (← read).q
  say "phase quote remaining body"
  let (bodyF, _) ← quoteE (.lam nm dom body .default)
  let some B := lamBody? bodyF | throwError "expected abstraction"
  let allF := mkAbbr ``Classicism.Meta.Term.forall' Γ #[σ, B]
  say "phase coerce previous instantiated formula to next universal"
  let memo ← IO.mkRef ({} : ConversionCache)
  let d ← tracedCoerce memo d F allF
  let stats ← memo.get
  say s!"cache terms={stats.terms.size} diffs={stats.diffs.size}"
  say "phase quote supplied order"
  let (a', _) ← quoteE a
  say "phase allEβ"
  let d ← rule ``Classicism.Meta.Derivable.allEβ #[Γ, Δ, σ, B, d, a']
  say "phase instE"
  return (instE Γ σ tyT B a', d)

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
          let rec enter (i : Nat) : TrM Unit := do
            if hi : i < xs.size then
              let x := xs[i]
              let ty ← inferType x
              if ← isProp ty then
                let f ← quoteF ty
                let dep ← depth
                withReader (fun ctx => {ctx with hyps := ⟨x.fvarId!,f,dep⟩ :: ctx.hyps}) (withCaches (enter (i+1)))
              else
                let ty' ← (Classicism.Meta.Quote.quoteTy ty).run (← read).q
                withReader (fun ctx => {ctx with q := {ctx.q with objVars := (x.fvarId!,ty') :: ctx.q.objVars}}) (withCaches (enter (i+1)))
            else
              let body := ((info.value! (allowOpaque := true)).beta xs).headBeta
              let fn := body.getAppFn
              let args := body.getAppArgs
              let mut count := 0
              for arg in args do
                if ← isParam arg then count := count+1 else break
              let params := args.extract 0 count
              let thm ← ensureSpecialized fn.constName! fn.constLevels! params
              let say (msg : String) : TrM Unit := IO.FS.withFile "/workspace/scratch/041abd450d63/work/Classicism-CH-recovery/diagnostic-cached-phased-feed.trace" .append (fun h => h.putStrLn msg)
              say "BEGIN contextual citation"
              let start ← IO.monoMsNow
              let (f,d) ← citeTheorem (mkAppN fn params) thm
              say s!"END contextual citation ms={(← IO.monoMsNow)-start}"
              let mut current := mkAppN fn params
              let mut formula := f
              let mut proof := d
              for j in [count:args.size] do
                let arg := args[j]!
                let argKind := if ← isProof arg then "proof" else "object"
                say s!"BEGIN argument {j-count} {argKind}"
                let start ← IO.monoMsNow
                let (ff,dd) ← if j-count == 2 then tracedObjectFeed current formula proof arg else feed current formula proof #[arg]
                current := mkApp current arg
                formula := ff
                proof := dd
                let st ← get
                say s!"END argument {j-count} ms={(← IO.monoMsNow)-start} quotes={st.quotes.size} nfs={st.nfs.size} shadows={st.shadows.size} interps={st.interps.size}"
          enter k
    go 0 []
  let _ ← (action.run {ax:=ax,axIsC:=false}).run {}
  if let some cert := (← getEnv).find? (c ++ `derivable) then
    emitMetric s!"{c} certificate_type" cert.type
    emitMetric s!"{c} certificate_proof" (cert.value! (allowOpaque := true))

run_cmd Lean.Elab.Command.liftTermElabM do
  probeQuote ``Classicism.MathematicalContingency.doubleHartogs_commonPairedBound_nontrivial
