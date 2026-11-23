import Lean
import Classicism.Semantics.Relational

/-!
# Quotation of statements

The first half of the translator from the strict layer into the metalogical one: `⌜·⌝`,
reading a strict **statement**, a Lean proposition, as a sentence of the object language.
`#classicism_quote foo` declares two things for a theorem `foo : p`:

* `foo.quoted : Ty → … → Sentence Signature.pure`, the sentence, with each of `foo`'s type
  parameters made a metalogical one (`σ' : Ty`); and
* `foo.reflect : ∀ σ …, Sentence.holds (Interp.ofDomain e) (foo.quoted σ …) = p[σ := ⟦σ⟧]`,
  proved by `rfl`, in the interpretation whose domain is the Lean type `e` itself, since
  the statement may mention it.

The second is the check. The quoter is a meta-program and not trusted; if it produced an
ill-typed sentence, or one whose reading differs from the statement, the reflection equation
would fail to elaborate or the kernel would reject `rfl`. What this establishes is the
sentence's **reading** in this one interpretation, up to definitional equality; it is not a
check of the syntax as such. The interpretation is not injective on syntax: in particular it
reads `e` and every type variable as the same Lean type `e`, so a quoted sentence with a type
variable where `e` belongs would pass. That gap is closed separately: every instance of a
principle's schema is shown to have only closed types, `P.X.schema_closedTypes`
(`Certified/Schemas.lean`), so no type variable occurs in a certified sentence. Beyond that,
the fidelity of the translation rests on the reflection equation and on reading the quoter.

## What is quoted

The vocabulary of strict statements: `Prop`, `e`, arrows, local variables, `∧`, `∨`, `¬`,
`∀`, `∃`, `=`, the paper's `imp`, `iff`, `Top`, `Bot`, `Box`, `Dia`, `everything`, and
λ-abstraction and application. Any other constant of this library is unfolded and the
result quoted; so a definition such as `P.Functionality.strict` quotes through its body.
A class operation of `SRel`, at any type, becomes the corresponding operation of
`Meta/Relational.lean`, defined by recursion on the type; at a concrete type that computes
to the pointwise formula, and at a type parameter it stays as `andR τ'` and the like.

Type parameters guarded by `Ty` become variables of type `Ty`; those guarded by `RelTy`,
`SRel`, `SOrder` or `SPointwise`, variables of type `RTy`, whose readings carry the strict layer's
instances by `instSRelDenote`. Reflection is then no longer `rfl` but rewriting with the
lemma for each operation, `reflect_by_rewriting`.
-/

open Lean Meta Elab Term Command

namespace Classicism.Meta.Quote

/-- How a Lean type parameter is read: as an object type, or as a relational one. -/
inductive Kind
  | ty
  | rty
  deriving BEq, Inhabited

/-- The reading of the local context: shallow type parameters to metalogical ones, and
Lean object variables, innermost first, to their object types. -/
structure QCtx where
  tyVars : List (FVarId × Kind × Expr) := []
  objVars : List (FVarId × Expr) := []

abbrev QM := ReaderT QCtx TermElabM

private def tyE : Expr := mkConst ``Classicism.Meta.Ty
private def rtyE : Expr := mkConst ``Classicism.Meta.RTy
private def relE (ρ : Expr) : Expr := mkApp (mkConst ``Classicism.Meta.Ty.rel) ρ
private def tE : Expr := relE (mkConst ``Classicism.Meta.RTy.t)

/-- Reduce a raw projection of anything but a variable: `whnfCore` projects out of a
constructor once the instance unfolds, and reducible unfolding is the fallback. -/
def reduceProj (f : Expr) : MetaM Expr := do
  let f' ← whnfCore f
  if f' != f then return f'
  let f' ← whnfR f
  if f' != f then return f'
  whnf f

/-- A raw projection `e.k` of a structure, as its projection function applied: the
structure's parameters, then `e`. -/
def projAsApp (S : Name) (k : Nat) (e : Expr) : MetaM (Option Expr) := do
  let some sinfo := getStructureInfo? (← getEnv) S | return none
  let some field := sinfo.fieldNames[k]? | return none
  let ty ← whnf (← inferType e)
  unless ty.isAppOf S do return none
  return some (mkAppN (mkConst (S ++ field)) (ty.getAppArgs ++ #[e]))

mutual

/-- Read a Lean type as an object type. -/
partial def quoteTy (e : Expr) : QM Expr := do
  let e ← instantiateMVars e
  match e with
  | .sort .zero => return tE
  | .const ``Classicism.e _ => return mkConst ``Classicism.Meta.Ty.e
  | .fvar id =>
    match (← read).tyVars.find? (·.1 == id) with
    | some (_, .ty, x) => return x
    | some (_, .rty, x) => return relE x
    | none => throwError "quote: the type {e} is not a parameter of the statement"
  | .forallE _ d b _ =>
    if b.hasLooseBVars then throwError "quote: a dependent type {e} is not a type of R"
    return relE (mkApp2 (mkConst ``Classicism.Meta.RTy.arr) (← quoteTy d) (← quoteRTy b))
  | .mdata _ b => quoteTy b
  | _ =>
    let e' ← whnfR e
    if e' != e then quoteTy e' else throwError "quote: {e} is not a type of R"

/-- Read a Lean type as a relational type. -/
partial def quoteRTy (e : Expr) : QM Expr := do
  let e ← instantiateMVars e
  match e with
  | .sort .zero => return mkConst ``Classicism.Meta.RTy.t
  | .fvar id =>
    match (← read).tyVars.find? (·.1 == id) with
    | some (_, .rty, x) => return x
    | _ => throwError "quote: {e} is not known to be a relational type"
  | .forallE _ d b _ =>
    if b.hasLooseBVars then throwError "quote: a dependent type {e} is not a type of R"
    return mkApp2 (mkConst ``Classicism.Meta.RTy.arr) (← quoteTy d) (← quoteRTy b)
  | .mdata _ b => quoteRTy b
  | _ =>
    let e' ← whnfR e
    if e' != e then quoteRTy e' else throwError "quote: {e} is not a relational type"

end

/-- The syntax of a de Bruijn index. -/
private def varStx : Nat → TermElabM (TSyntax `term)
  | 0 => `(Classicism.Meta.Var.zero)
  | n + 1 => do `(Classicism.Meta.Var.succ $(← varStx n))

/-- Enter a binder over an object variable. -/
private def withObj {α} (nm : Name) (ty : Expr) (k : Expr → QM α) : QM α := do
  let σ ← quoteTy ty
  withLocalDeclD nm ty fun x =>
    withReader (fun c => { c with objVars := (x.fvarId!, σ) :: c.objVars }) (k x)

mutual

/-- A relational operation of the strict layer's class `SRel`, at the type `τ`: the
object-language constant `op τ'` of `Meta/Term.lean` applied to the arguments, when `τ`
is a type parameter; at a constructor type the strict instance unfolds and the operation
is read through it, so the constants stand only at type parameters. -/
partial def relOp (e τ : Expr) (op : Name) (args : Array Expr) : QM (TSyntax `term) := do
  let ρ ← quoteRTy τ
  if ρ.isConstOf ``Classicism.Meta.RTy.t || ρ.isAppOfArity ``Classicism.Meta.RTy.arr 2 then
    -- a constructor type: the instance unfolds, and the operation is read through it
    let e' ← match ← unfoldDefinition? e with
      | some e' => pure e'
      | none => whnfR e
    if e' == e then throwError "quote: the operation {e} at a constructor type does not unfold"
    return ← quoteTerm e'
  let ρs ← exprToSyntax ρ
  let mut acc ← `($(mkIdent op) $ρs)
  for a in args do
    acc ← `(Classicism.Meta.Term.app $acc $(← quoteTerm a))
  return acc

/-- Read a strict statement, or a subterm of one, as the syntax of an object term. -/
partial def quoteTerm (e : Expr) : QM (TSyntax `term) := do
  let e ← instantiateMVars e
  match e with
  | .mdata _ b => quoteTerm b
  | .letE _ _ v b _ => quoteTerm (b.instantiate1 v)
  | .proj S k b =>
    if b.isFVar then
      let some e' ← projAsApp S k b | throwError "quote: cannot read the projection {e}"
      quoteTerm e'
    else
      let e' ← reduceProj e
      if e' == e then throwError "quote: cannot reduce the projection {e}"
      quoteTerm e'
  | .fvar id =>
    let some i := (← read).objVars.findIdx? (·.1 == id)
      | throwError "quote: the variable {e} is not an object variable in scope"
    `(Classicism.Meta.Term.var $(← varStx i))
  | .lam nm d b _ =>
    withObj nm d fun x => do
      let b' ← quoteTerm (b.instantiate1 x)
      `(Classicism.Meta.Term.lam $b')
  | .forallE nm d b _ =>
    if ← isProp d then
      if b.hasLooseBVars then throwError "quote: a formula depends on a proof: {e}"
      let d' ← quoteTerm d
      if b.isConstOf ``False then `(Classicism.Meta.Term.neg $d')
      else `(Classicism.Meta.Term.imp $d' $(← quoteTerm b))
    else
      let σ ← quoteTy d
      let σs ← exprToSyntax σ
      withObj nm d fun x => do
        let b' ← quoteTerm (b.instantiate1 x)
        `(Classicism.Meta.Term.forall' (σ := $σs) $b')
  | _ =>
    match e.getAppFnArgs with
    | (``And, #[a, b]) => do `(Classicism.Meta.Term.conj $(← quoteTerm a) $(← quoteTerm b))
    | (``Or, #[a, b]) => do `(Classicism.Meta.Term.disj $(← quoteTerm a) $(← quoteTerm b))
    | (``Not, #[a]) => do `(Classicism.Meta.Term.neg $(← quoteTerm a))
    | (``Classicism.imp, #[a, b]) => do `(Classicism.Meta.Term.imp $(← quoteTerm a) $(← quoteTerm b))
    | (``Classicism.iff, #[a, b]) => do `(Classicism.Meta.Term.iff $(← quoteTerm a) $(← quoteTerm b))
    | (``True, #[]) => `(Classicism.Meta.Term.top)
    | (``False, #[]) => `(Classicism.Meta.Term.bot)
    | (``Classicism.Box, #[a]) => do `(Classicism.Meta.Term.box $(← quoteTerm a))
    | (``Classicism.Dia, #[a]) => do `(Classicism.Meta.Term.dia $(← quoteTerm a))
    | (``Iff, #[a, b]) => do `(Classicism.Meta.Term.iff $(← quoteTerm a) $(← quoteTerm b))
    | (``Eq, #[α, a, b]) => do
      let σs ← exprToSyntax (← quoteTy α)
      `(Classicism.Meta.Term.eq' (σ := $σs) $(← quoteTerm a) $(← quoteTerm b))
    | (``Exists, #[α, .lam nm d b _]) => do
      let _ := α
      let σs ← exprToSyntax (← quoteTy d)
      withObj nm d fun x => do
        let b' ← quoteTerm (b.instantiate1 x)
        `(Classicism.Meta.Term.exists' (σ := $σs) $b')
    | (``Exists, #[α, F]) => do
      -- `∃ F` with `F` not a lambda: `∃σ F`
      let σs ← exprToSyntax (← quoteTy α)
      `(Classicism.Meta.Term.app (Classicism.Meta.Term.ex $σs) $(← quoteTerm F))
    | (``Classicism.Rel.constP, #[τ, _, p]) => relOp e τ ``Classicism.Meta.Term.constR #[p]
    | (``Classicism.Rel.neg, #[τ, _, X]) => relOp e τ ``Classicism.Meta.Term.negR #[X]
    | (``Classicism.Rel.and, #[τ, _, X, Y]) => relOp e τ ``Classicism.Meta.Term.andR #[X, Y]
    | (``Classicism.Rel.or, #[τ, _, X, Y]) => relOp e τ ``Classicism.Meta.Term.orR #[X, Y]
    | (``Classicism.Rel.coext, #[τ, _, X, Y]) => relOp e τ ``Classicism.Meta.Term.coextR #[X, Y]
    | (``Classicism.Rel.boxAt, #[τ, _, X]) => relOp e τ ``Classicism.Meta.Term.boxR #[X]
    | (``Classicism.Rel.incl, #[τ, _, X, Y]) => relOp e τ ``Classicism.Meta.Term.inclR #[X, Y]
    | (``Eq, args) =>
      -- identity unapplied or partially applied, as η-reduction of `fun z => a = z` leaves it
      let σs ← exprToSyntax (← quoteTy args[0]!)
      let mut acc ← `(Classicism.Meta.Term.eq $σs)
      for a in args.extract 1 args.size do
        acc ← `(Classicism.Meta.Term.app $acc $(← quoteTerm a))
      return acc
    | (``Exists, #[α]) => do
      let σs ← exprToSyntax (← quoteTy α)
      `(Classicism.Meta.Term.ex $σs)
    | (``And, args) | (``Or, args) | (``Not, args) =>
      -- a connective unapplied or partially applied
      let c := e.getAppFn.constName!
      let mut acc ← if c == ``And then `(Classicism.Meta.Term.and)
        else if c == ``Or then `(Classicism.Meta.Term.or) else `(Classicism.Meta.Term.not)
      for a in args do
        acc ← `(Classicism.Meta.Term.app $acc $(← quoteTerm a))
      return acc
    | _ =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .proj S k b := f then
        -- an applied raw projection: of an instance variable, as the projection
        -- function applied; of anything else, reduced
        if b.isFVar then
          let some f' ← projAsApp S k b | throwError "quote: cannot read the projection {f}"
          return ← quoteTerm (mkAppN f' args)
        else
          let f' ← reduceProj f
          if f' == f then throwError "quote: cannot reduce the projection {f}"
          return ← quoteTerm (mkAppN f' args)
      if f.isFVar then
        -- an object variable applied to arguments
        let mut acc ← quoteTerm f
        for a in args do
          acc ← `(Classicism.Meta.Term.app $acc $(← quoteTerm a))
        return acc
      if f.isLambda then
        return ← quoteTerm (e.headBeta)
      -- anything else: unfold one step and try again, so that this library's definitions
      -- and its instances at concrete types quote through their bodies
      match ← unfoldDefinition? e with
      | some e' =>
        if let .proj _ _ b := e'.getAppFn then
          if b.isFVar then throwError "quote: no reading of the field {f} of an instance variable"
        quoteTerm e'
      | none =>
        let e' ← whnfCore e
        if e' != e then quoteTerm e'
        else
          -- a projection of an instance at a concrete type reduces under `whnfR`
          let e'' ← whnfR e
          if e'' != e then quoteTerm e''
          else throwError "quote: cannot read {e} as an object term"

end

/-- The simp set for reflection of a shallow statement: the readings of the syntax, the
readings of the type-subscripted operations as the shallow classes' operations (by the
lemmas of `Meta/Relational.lean`), and the shallow connectives' identifications with the
object readings. Definitions of the shallow layer that the statement uses are added per
statement by `reflectDefs`. -/
def reflectSimpSet : Array Name :=
  #[``Classicism.Meta.Sentence.holds, ``Classicism.Meta.Term.denote, ``Classicism.Meta.Var.denote,
    ``Classicism.Meta.RTy.constD_eq_rel, ``Classicism.Meta.RTy.negD_eq_rel,
    ``Classicism.Meta.RTy.andD_eq_rel, ``Classicism.Meta.RTy.orD_eq_rel,
    ``Classicism.Meta.RTy.coextD_eq_rel, ``Classicism.Meta.RTy.boxD_eq_rel,
    ``Classicism.Meta.RTy.inclD_eq_rel, ``Classicism.Meta.Term.denote_weaken,
    ``Classicism.imp, ``Classicism.iff, ``Classicism.Box, ``Classicism.Dia,
    ``Classicism.Rel.top, ``Classicism.Rel.bot, ``Classicism.Rel.le,
    ``Classicism.Meta.top_eq, ``Classicism.Meta.bot_eq, ``Classicism.Meta.imp_eq,
    ``Classicism.Meta.iff_eq, ``Classicism.Meta.iff_eq', ``Classicism.Meta.box_eq]

/-- The definitions of this library that a statement uses, transitively through their
bodies: what reflection must unfold on the statement's side. Instances are included,
since an operation at a concrete type reads through its instance; theorems are not. -/
partial def reflectDefs (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut todo := e.getUsedConstants.toList
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    unless (`Classicism).isPrefixOf c && !(`Classicism.Meta).isPrefixOf c do continue
    match env.find? c with
    | some (.defnInfo v) =>
      out := out.push c
      todo := v.value.getUsedConstants.toList ++ todo
    | _ => pure ()
  return out

/-! ### The command -//-! ### The command -/

/-- The `Ty` marker instance at a type. -/
private def tyMk (σ : Expr) : Expr :=
  mkApp2 (mkConst ``Classicism.Ty.mk) σ (mkConst ``Unit.unit)
private def relTyMk (σ : Expr) : Expr :=
  mkApp2 (mkConst ``Classicism.RelTy.mk) σ (mkConst ``Unit.unit)

/-- Quote the statement `ty`. Returns the quoted sentence as a function of the type
parameters, and the reflection statement and its proof. -/
def quoteStatement (ty : Expr) : TermElabM (Expr × Expr × Expr) := do
  forallTelescope ty fun xs body => do
    -- classify the leading parameters
    let mut k := 0
    let mut kinds : Array (Expr × Kind) := #[]
    let mut insts : Array Expr := #[]
    for x in xs do
      let t ← whnf (← inferType x)
      if t.isSort && !t.isProp then
        kinds := kinds.push (x, .ty); k := k + 1
      else if let some cls := (← isClass? t) then
        let σ := t.getAppArgs[0]!
        if cls == ``Classicism.Ty then pure ()
        else if cls == ``Classicism.RelTy || cls == ``Classicism.Rel || cls == ``Classicism.Order
            || cls == ``Classicism.Pointwise then
          -- a relational guard on a parameter makes it a Rel-parameter
          if let some idx := kinds.findIdx? (·.1 == σ) then kinds := kinds.set! idx (σ, .rty)
        else throwError "quote: a parameter of class {cls} has no object-language reading"
        insts := insts.push x; k := k + 1
      else break
    let stmt ← mkForallFVars (xs.extract k xs.size) body
    -- metalogical type parameters, one per shallow one
    let rec go (i : Nat) (ctx : QCtx) (tvs : Array Expr) : TermElabM (Expr × Expr × Expr) := do
      if h : i < kinds.size then
        let (σ, kind) := kinds[i]
        let tyOfKind := if kind == .ty then tyE else rtyE
        withLocalDeclD ((← σ.fvarId!.getUserName).appendAfter "'") tyOfKind fun tv =>
          go (i + 1) { ctx with tyVars := (σ.fvarId!, kind, tv) :: ctx.tyVars } (tvs.push tv)
      else
        let stx ← (quoteTerm stmt).run ctx
        let sentenceTy := mkApp (mkConst ``Classicism.Meta.Sentence) (mkConst ``Classicism.Meta.Signature.pure)
        let sentence ← elabTermEnsuringType stx (some sentenceTy)
        synthesizeSyntheticMVarsNoPostponing
        let sentence ← instantiateMVars sentence
        if sentence.hasMVar then throwError "quote: the sentence has unresolved holes:{indentExpr sentence}"
        let quoted ← mkLambdaFVars tvs sentence
        -- the reflection statement: `e` reads as the Lean type `e`, since the statement
        -- mentions it, and the type parameters read as `⟦σ'⟧` over that domain
        let D : Expr := Expr.const ``Classicism.e []
        do
          let I := mkApp (mkConst ``Classicism.Meta.Interp.ofDomain) D
          let lhs := mkApp3 (mkConst ``Classicism.Meta.Sentence.holds)
            (mkConst ``Classicism.Meta.Signature.pure) I (mkAppN quoted tvs)
          -- instantiate the original statement's parameters, one binder at a time: a type
          -- parameter by the reading of its metalogical parameter, an instance by the marker
          let mut rhs := ty
          let mut ti := 0
          for _ in [0:k] do
            let .forallE _ d b _ := rhs | throwError "quote: internal error in the telescope"
            let d ← whnf d
            let arg ← if d.isSort then
                let (_, kind) := kinds[ti]!
                let tv := tvs[ti]!
                ti := ti + 1
                pure (if kind == .ty then mkApp2 (mkConst ``Classicism.Meta.Ty.denote) D tv
                  else mkApp2 (mkConst ``Classicism.Meta.RTy.denote) D tv)
              else
                let cls := d.getAppFn.constName!
                let subject := d.getAppArgs[0]!
                if cls == ``Classicism.Ty then pure (tyMk subject)
                else if cls == ``Classicism.RelTy then pure (relTyMk subject)
                else
                  -- `Rel`/`Order`/`Pointwise` on the reading of a Rel-parameter: the
                  -- recursive instances of `Meta/Relational.lean`
                  let some (_, ρ) := subject.app2? ``Classicism.Meta.RTy.denote
                    | throwError "quote: an instance of {cls} on {subject}, which is not the reading of a type parameter"
                  if cls == ``Classicism.Rel then
                    pure (mkApp2 (mkConst ``Classicism.Meta.instRelDenote) D ρ)
                  else if cls == ``Classicism.Order then
                    pure (mkApp2 (mkConst ``Classicism.Meta.instOrderDenote) D ρ)
                  else pure (mkApp2 (mkConst ``Classicism.Meta.instPointwiseDenote) D ρ)
            rhs := b.instantiate1 arg
          let eq ← mkEq lhs rhs
          let reflectTy ← mkForallFVars tvs eq
          -- by `rfl` when the two sides are definitionally equal, which they are unless a
          -- relational operation sits at a type parameter; otherwise by rewriting with the
          -- lemmas of `Meta/Relational.lean`, one per operation, proved by induction
          let reflectVal ←
            if ← withReducible (pure ()) *> isDefEq lhs rhs then
              mkLambdaFVars tvs (← mkEqRefl lhs)
            else
              let defs ← reflectDefs rhs
              let lemmas ← (reflectSimpSet ++ defs).mapM fun n =>
                `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
              let stx ← `(by intros; simp only [$lemmas,*]; try rfl)
              let v ← Term.withoutErrToSorry do
                let v ← elabTermEnsuringType stx (some reflectTy)
                synthesizeSyntheticMVarsNoPostponing
                instantiateMVars v
              if v.hasSorry then throwError "quote: reflection by rewriting failed"
              pure v
          return (quoted, reflectTy, reflectVal)
    go 0 {} #[]

/-- Declare `n.quoted` and `n.reflect` from the results of `quoteStatement`. -/
def declareQuoted (n : Name) (quoted reflectTy reflectVal : Expr) : TermElabM Unit := do
  let quotedTy ← inferType quoted
  let dv : DefinitionVal := { name := n ++ `quoted, levelParams := [], type := quotedTy, value := quoted, hints := .abbrev, safety := .safe }
  let tv : TheoremVal := { name := n ++ `reflect, levelParams := [], type := reflectTy, value := reflectVal }
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl dv)
    addDecl (.thmDecl tv)

/-- `#classicism_quote foo …` quotes the statement of each theorem, declaring `foo.quoted`
and the reflection theorem `foo.reflect`, checked by `rfl`. -/
syntax (name := classicismQuote) "#classicism_quote " ident+ : command

@[command_elab classicismQuote] def elabQuote : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    let info ← getConstInfo n
    try
      let (quoted, reflectTy, reflectVal) ← liftTermElabM (quoteStatement info.type)
      liftTermElabM (declareQuoted n quoted reflectTy reflectVal)
      logInfo m!"{n} ⟶ {n ++ `quoted}:{indentExpr (← getConstInfo (n ++ `quoted)).value!}\nreflects ✓"
    catch ex =>
      logError m!"{n}: not quoted — {ex.toMessageData}"

/-- `#classicism_quote_audit Mod …` quotes every theorem of the modules whose name ends in
`strict`, and reports. -/
syntax (name := classicismQuoteAudit) "#classicism_quote_audit " ident+ : command

@[command_elab classicismQuoteAudit] def elabQuoteAudit : CommandElab := fun stx => do
  for modId in stx[1].getArgs do
    let env ← getEnv
    let some idx := env.getModuleIdx? modId.getId
      | logError m!"no module {modId.getId}"; continue
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .thmInfo _ := ci then
          if n.components.getLast? == some `strict then names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    let mut ok : Nat := 0
    let mut failures : Array MessageData := #[]
    for n in names do
      let info ← getConstInfo n
      try
        let (quoted, reflectTy, reflectVal) ← liftTermElabM (quoteStatement info.type)
        liftTermElabM (declareQuoted n quoted reflectTy reflectVal)
        ok := ok + 1
      catch ex =>
        failures := failures.push m!"{n}: {ex.toMessageData}"
    logInfo m!"{modId.getId}: {ok} of {names.size} strict statements quoted and reflected\n\
{MessageData.joinSep failures.toList "\n"}"

end Classicism.Meta.Quote
