import Classicism.Tools.Quote
import Classicism.Syntax.Normalize

/-!
# Translation of shallow proofs into derivations

The translator. `#classicism_derive foo` reads the proof term of a gated shallow theorem
`foo` and declares

    foo.derivable : ∀ σ' …, Theorem C.axioms(Minus) (foo.quoted σ' …)

a derivation, in the metalogical layer's system, of the sentence the quoter makes of
`foo`'s statement, with the theorem's type parameters read as metalogical ones (`σ' : Ty`, `τ' : RTy`). The kernel
checks it. So, for each theorem it reaches, the chain is two links: a proof in Lean under
the gate of `Classicism/Check.lean`, and a derivation in `H` closed under Subst as an
object of Lean, the translator untrusted.

## What a gated shallow proof is made of

A proof term under the gate is natural-deduction shaped already. Its constants are the
logical inductives' constructors, eliminators and recursors (`And.intro`, `Or.elim`,
`Exists.casesOn`, …), the identity plumbing that `rw` and `▸` emit (`Eq.mpr`, `congrArg`,
`Eq.ndrec`, …), lambdas over hypotheses and over objects, applications, the axioms `em`
and `e_exists`, theorems of this library, and the two gated primitives. Each of the first
kinds is one rule of `Derivable`, or a derived rule of `Derivation.lean`; a cited theorem
is translated once, generically, and cited by name; and the two primitives are where the
gate pays off: `propext h`, whose `h` mentions no hypothesis, is **Subst** at the hole
`P = ⬚` with the two directions of `h` as its premises, and `funext (fun x => h)` is
`substEq`, the induction on the type that carries Subst to identities at every type.
The premises of a Subst are derived at the *logical part* of the axiom set, since that is
what the rule asks; a theorem cited there is lifted into it.

A class law used at a type parameter — `Rel.and_constP_true` at `τ`, `Order.le_iff`,
a law of `Pointwise` — is not an axiom: it is derived once for every object type by
induction on the type, the `Prop` instance's proof the base case and the arrow instance's
the step (`ensureFieldInduction`).

## Conversion

Lean's kernel converts silently; the object language has the rule `conv`. Where a term's
quotation and the quotation of its type differ by βηδ, the translator supplies the
conversion, checked by the verified normalizer of `Normalize.lean` through its untyped
shadow of the syntax.
-/

open Lean Meta Elab Term Command Classicism.Meta.Quote

/-- The arity, instance included, of each relational operation of `Rel`, for reading a
partial application of one. -/
def relOpArity? : Name → Option Nat
  | ``Classicism.Rel.constP | ``Classicism.Rel.neg | ``Classicism.Rel.boxAt => some 3
  | ``Classicism.Rel.and | ``Classicism.Rel.or | ``Classicism.Rel.coext
  | ``Classicism.Rel.incl => some 4
  | _ => none

namespace Classicism.Meta.Translate

register_option Classicism.Meta.Translate.check : Bool := {
  defValue := false
  descr := "type-check every node the translator builds (slow; for debugging)"
}

register_option Classicism.Meta.Translate.convAxiom : Bool := {
  defValue := false
  descr := "for measurement only: replace every conversion proof by `sorryAx`, to see what the conversions cost the kernel"
}

register_option Classicism.Meta.Translate.profile : Bool := {
  defValue := false
  descr := "print the time the translator spent in each phase"
}

register_option Classicism.Meta.Translate.progress : String := {
  defValue := ""
  descr := "a file to which `#classicism_derive_audit` appends a line per theorem as it \
    goes; Lean captures what elaboration prints, so a long run cannot be watched otherwise"
}

/-- A shadow of an object term: the syntax without its contexts, so that the context,
which every constructor of the typed syntax carries, plays no part in comparison, but
with the types of binders and applications, so that a shadow can be written back as
syntax. A logical constant is read by name with its type index. -/
inductive Tm where
  | var (i : Nat)
  /-- `app σ ρ f a`, with `f : σ ⇒ ρ`. -/
  | app (σ ρ : Expr) (f a : Tm)
  /-- `lam σ ρ b`, with `b : ρ` under a variable of type `σ`. -/
  | lam (σ ρ : Expr) (b : Tm)
  | const (n : Name) (ty : Expr)
  /-- Anything not a constructor of the syntax after `whnf`, kept as it is, in its context. -/
  | opaque (Γ : Expr) (e : Expr)
  deriving BEq, Hashable, Inhabited, Repr

namespace Tm

/-- Shift the free variables at or above `c` by `d`. -/
partial def shift (d : Nat) (c : Nat) : Tm → Tm
  | var i => if i ≥ c then var (i + d) else var i
  | app σ ρ f a => app σ ρ (shift d c f) (shift d c a)
  | lam σ ρ b => lam σ ρ (shift d (c + 1) b)
  | t => t

/-- Substitute `s` for the variable `j`, lowering those above it. -/
partial def subst (j : Nat) (s : Tm) : Tm → Tm
  | var i => if i == j then s else if i > j then var (i - 1) else var i
  | app σ ρ f a => app σ ρ (subst j s f) (subst j s a)
  | lam σ ρ b => lam σ ρ (subst (j + 1) (shift 1 0 s) b)
  | t => t

/-- Does the variable `j` occur free? -/
partial def occurs (j : Nat) : Tm → Bool
  | var i => i == j
  | app _ _ f a => occurs j f || occurs j a
  | lam _ _ b => occurs (j + 1) b
  | _ => false

/-- Lower the free variables above `j` by one, `j` itself not occurring. -/
partial def lower (j : Nat) : Tm → Tm
  | var i => if i > j then var (i - 1) else var i
  | app σ ρ f a => app σ ρ (lower j f) (lower j a)
  | lam σ ρ b => lam σ ρ (lower (j + 1) b)
  | t => t

/-- η-reduce at the root, as `Term.etaRed` does. -/
def etaRed : Tm → Tm
  | lam σ ρ (app σ' ρ' g (var 0)) => if occurs 0 g then lam σ ρ (app σ' ρ' g (var 0)) else lower 0 g
  | t => t

/-- One pass, exactly as `Term.step` computes it: parallel β, with η at each abstraction.
The type-subscripted operations are constants here as for the kernel. -/
partial def step : Tm → Tm
  | app σ ρ f a =>
    match step f with
    | lam _ _ b => subst 0 (step a) b
    | f' => app σ ρ f' (step a)
  | lam σ ρ b => etaRed (lam σ ρ (step b))
  | t => t

/-- The normal form, and the number of passes of `step` that reach it: the fuel to give
`Term.nf` so that the kernel does no more work than needed. -/
partial def normalize (t : Tm) (fuel : Nat := 0) : Option (Tm × Nat) :=
  -- typed terms normalize, but a shadow is untyped; a runaway is cut off rather than
  -- allowed to eat the machine
  if fuel > 500 then none else
  let t' := step t
  if t' == t then some (t, fuel) else normalize t' (fuel + 1)

/-- Is the constant a type-subscripted operation? -/
def isRelOp (n : Name) : Bool :=
  n == ``Classicism.Meta.Term.constR || n == ``Classicism.Meta.Term.negR
    || n == ``Classicism.Meta.Term.andR || n == ``Classicism.Meta.Term.orR
    || n == ``Classicism.Meta.Term.coextR || n == ``Classicism.Meta.Term.boxR
    || n == ``Classicism.Meta.Term.inclR

end Tm

/-- One hypothesis in scope: its Lean variable, its object formula as quoted when it was
introduced, and how many object variables were then in scope. -/
structure Hyp where
  fvar : FVarId
  formula : Expr
  depth : Nat
  deriving Inhabited

structure TCtx where
  q : QCtx := {}
  hyps : List Hyp := []
  /-- The axiom set, `C.axioms` or `C.axiomsMinus`. -/
  ax : Expr
  axIsC : Bool
  /-- How many times inside the premises of a Subst: the current axiom set is `ax.logical`
  that many times over, and a theorem cited here is lifted into it. -/
  logicalDepth : Nat := 0
  /-- Induction hypotheses in scope, while a class law is being derived by induction on
  the object type: for the instance variable and field index, a proof of the law at the
  smaller type, a `Theorem`. -/
  ihs : List (FVarId × Nat × Expr) := []
  /-- The object context as a `List Ty`, cached; rebuilt at each binder. -/
  ctxCache : Expr := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Classicism.Meta.Ty)
  /-- The hypotheses as a `List (Formula Sig Γ)`, cached; rebuilt at each binder. -/
  hypsCache : Expr := mkApp (mkConst ``List.nil [Level.zero])
    (mkApp2 (mkConst ``Classicism.Meta.Formula) (mkConst ``Classicism.Meta.Signature.pure)
      (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Classicism.Meta.Ty)))

structure TState where
  /-- Specializations in progress, to catch a theorem citing itself. -/
  specs : Std.HashSet String := {}
  /-- Milliseconds spent, by phase, for the profile the command prints. -/
  timing : Std.HashMap String Nat := {}
  /-- Quotations already made, by object context and Lean expression. -/
  quotes : Std.HashMap (Expr × Expr) (Expr × Expr) := {}
  /-- Shadows of object terms, normalized, with the passes it took, by expression. -/
  nfs : Std.HashMap Expr (Tm × Nat) := {}
  /-- Normal forms of shadows, with the passes it took, by shadow. -/
  nfMemo : Std.HashMap Tm (Tm × Nat) := {}
  /-- Normalized type expressions, by expression. -/
  normTys : Std.HashMap Expr Expr := {}
  /-- Shadows already read, by expression. -/
  shadows : Std.HashMap Expr Tm := {}
  /-- Derivations already made, by object context, hypotheses and proof term. A strict
  proof term is a DAG whose tree can be hundreds of times larger (`ll_lam`: 4,407 nodes
  shared, 1,516,016 as a tree), and the walk must be over the DAG.

  The memo tables are restored at the end of each nested declaration (a cited lemma's
  generic translation, a specialization, a law by induction): what they hold for the
  nested proof is of no use to the enclosing one, and keeping it across every cited
  lemma made one run grow past six gigabytes while the same lemmas, derived one per
  command, peaked at 664 MB. -/
  interps : Std.HashMap (Expr × Expr × Expr) (Expr × Expr) := {}
  /-- Phases being timed, so that a recursive phase is not counted once per level. -/
  activePhases : Std.HashSet String := {}
  /-- The quoter's recursion depth, to report a loop with its expression. -/
  qdepth : Nat := 0

abbrev TrM := ReaderT TCtx (StateRefT TState TermElabM)

/-- The axiom set of the current position: the run's set, or its logical part when inside
the premises of a Subst. -/
def curAx : TrM Expr := do
  let c ← read
  let mut ax := c.ax
  for _ in [0:c.logicalDepth] do
    ax := mkAppN (mkConst ``Classicism.Meta.AxiomSet.logical) #[mkConst ``Classicism.Meta.Signature.pure, ax]
  return ax

/-- Enter the premises of a Subst: no hypotheses, the logical part of the axiom set. -/
def withLogical {α} (k : TrM α) : TrM α :=
  withReader (fun c => { c with logicalDepth := c.logicalDepth + 1, hyps := [] }) k

/-- Restore the memo tables to `saved`, keeping the bookkeeping that spans declarations
(the specializations in progress and the profile). Called at the end of a nested
declaration; see `TState.interps`. -/
def restoreMemo (saved : TState) : TrM Unit :=
  modify fun s => { saved with specs := s.specs, timing := s.timing }

/-- Time an action, under a phase name; an action already inside its phase is not timed
again. -/
def timed {α} (phase : String) (k : TrM α) : TrM α := do
  if (← get).activePhases.contains phase then k else
  modify fun s => { s with activePhases := s.activePhases.insert phase }
  let t₀ ← IO.monoMsNow
  try k finally
    let t₁ ← IO.monoMsNow
    modify fun s => { s with
      timing := s.timing.insert phase (s.timing.getD phase 0 + (t₁ - t₀))
      activePhases := s.activePhases.erase phase }

/-- A trace line, when profiling: to the progress file if one is set, since Lean holds
what elaboration prints until the command ends; else to stderr. -/
def trace (line : String) : TrM Unit := do
  unless Classicism.Meta.Translate.profile.get (← getOptions) do return
  let f := Classicism.Meta.Translate.progress.get (← getOptions)
  if f == "" then IO.eprintln line
  else IO.FS.withFile f .append fun h => h.putStrLn line

/-! ### Expressions of the object syntax -/

def sigE : Expr := mkConst ``Classicism.Meta.Signature.pure
def tyE : Expr := mkConst ``Classicism.Meta.Ty
def rtE : Expr := mkConst ``Classicism.Meta.RTy.t
def tRel (ρ : Expr) : Expr := mkApp (mkConst ``Classicism.Meta.Ty.rel) ρ
def tyT : Expr := tRel rtE
def tArr (σ ρ : Expr) : Expr := mkApp2 (mkConst ``Classicism.Meta.RTy.arr) σ ρ

/-- Is the relational type `t` or an arrow, rather than a type parameter? -/
def isConstructorRTy (ρ : Expr) : Bool :=
  ρ.isConstOf ``Classicism.Meta.RTy.t || ρ.isAppOfArity ``Classicism.Meta.RTy.arr 2

/-- Split an object type `Ty.rel (σ ⇒ ρ)`. -/
partial def splitArrow (T : Expr) : TrM (Expr × Expr) := do
  let T ← instantiateMVars T
  if let some ρ := T.app1? ``Classicism.Meta.Ty.rel then
    if let some (σ, ρ') := ρ.app2? ``Classicism.Meta.RTy.arr then return (σ, ρ')
  let T' ← whnf T
  if T' != T then splitArrow T' else
  throwError "derive: {T} is not an arrow type"

/-- The relational type of an object type `Ty.rel ρ`. -/
partial def relOf (T : Expr) : TrM Expr := do
  let T ← instantiateMVars T
  if let some ρ := T.app1? ``Classicism.Meta.Ty.rel then return ρ
  let T' ← whnf T
  if T' != T then relOf T' else throwError "derive: {T} is not a relational type"

def mkTApp (Γ σ ρ f a : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.app) #[sigE, Γ, σ, ρ, f, a]
def mkTLam (Γ σ ρ b : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.lam) #[sigE, Γ, σ, ρ, b]
def mkTVar (Γ σ v : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.var) #[sigE, Γ, σ, v]
/-- An abbreviation of `Classicism/Meta/Term.lean`, `conj p q` and the like, in context. -/
def mkAbbr (n : Name) (Γ : Expr) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[sigE, Γ] ++ args)
/-- The type of a type-subscripted operation at `ρ`: `t ⇒ ρ` for the constant relation,
`ρ ⇒ ρ` for negation and the box, `ρ ⇒ ρ ⇒ ρ` for conjunction and disjunction, and
`ρ ⇒ ρ ⇒ t` for coextension and implication. -/
def relOpType (n : Name) (ρ : Expr) : Expr :=
  if n == ``Classicism.Meta.Term.constR then tRel (tArr tyT ρ)
  else if n == ``Classicism.Meta.Term.negR || n == ``Classicism.Meta.Term.boxR then tRel (tArr (tRel ρ) ρ)
  else if n == ``Classicism.Meta.Term.andR || n == ``Classicism.Meta.Term.orR then
    tRel (tArr (tRel ρ) (tArr (tRel ρ) ρ))
  else tRel (tArr (tRel ρ) (tArr (tRel ρ) rtE))

/-- A type-subscripted operation applied: the constant `andR ρ` of `Classicism/Meta/Term.lean`,
then `app` for each operand. -/
def mkRel (n : Name) (ρ Γ : Expr) (args : Array Expr) : Expr := Id.run do
  let mut acc := mkAppN (mkConst n) #[sigE, Γ, ρ]
  let mut T := relOpType n ρ
  for a in args do
    let some ρ' := T.app1? ``Classicism.Meta.Ty.rel | return acc
    let some (σ, ρ'') := ρ'.app2? ``Classicism.Meta.RTy.arr | return acc
    acc := mkTApp Γ σ ρ'' acc a
    T := tRel ρ''
  return acc

/-- The object context from the `i`-th innermost variable outward, as a `List Ty`. -/
def ctxFrom (i : Nat) : TrM Expr := do
  let vars := (← read).q.objVars.drop i
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) tyE
  for (_, σ) in vars.reverse do
    acc := mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, acc]
  return acc

/-- The object context, innermost first, as a `List Ty`. -/
def ctxE : TrM Expr := return (← read).ctxCache

def depth : TrM Nat := return (← read).q.objVars.length

/-- The variable at de Bruijn index `i`, of type `σ`. -/
def varE (i : Nat) (σ : Expr) : TrM Expr := do
  let vars := (← read).q.objVars.toArray
  let mut v := mkAppN (mkConst ``Classicism.Meta.Var.zero) #[← ctxFrom (i + 1), σ]
  for j in [0:i] do
    let j := i - 1 - j
    v := mkAppN (mkConst ``Classicism.Meta.Var.succ) #[← ctxFrom (j + 1), σ, vars[j]!.2, v]
  return v

/-- `a.weaken` at the new variable's type `τ`, in the context `Γ` of `a`. -/
def weakenE (Γ τ σ a : Expr) : Expr :=
  mkAppN (mkConst ``Classicism.Meta.Term.weaken) #[sigE, Γ, τ, σ, a]

/-- β-reduce every redex in an expression, so that a codomain mentioning a bound proof
only through a motive's redex, `(fun _ => C) h`, is seen not to depend on it. -/
partial def betaDeep (e : Expr) : Expr :=
  e.replace fun t => if t.isHeadBetaTarget then some (betaDeep t.headBeta) else none

/-- The body of a quoted abstraction `Term.lam Sig Γ σ ρ b`, if it is one. -/
def lamBody? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Classicism.Meta.Term.lam 5 then some e.appArg! else none

/-- `b.instantiate a`. -/
def instE (Γ σ τ b a : Expr) : Expr :=
  mkAppN (mkConst ``Classicism.Meta.Term.instantiate) #[sigE, Γ, σ, τ, b, a]

/-- `a.close` into the context `Γ`. -/
def closeE (Γ σ a : Expr) : Expr :=
  mkAppN (mkConst ``Classicism.Meta.Term.close) #[sigE, Γ, σ, a]

/-- A hypothesis' formula in the current context: weakened once per object variable
introduced since it. -/
def hypFormula (h : Hyp) : TrM Expr := do
  let mut f := h.formula
  let vars := (← read).q.objVars.reverse
  for k in [h.depth:vars.length] do
    let Γ ← ctxFrom (vars.length - k)
    f := weakenE Γ vars[k]!.2 tyT f
  return f

/-- The hypotheses as a `List (Formula Sig Γ)`, computed afresh. -/
def hypsList : TrM Expr := do
  let Γ ← ctxFrom 0
  let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) fty
  for h in (← read).hyps.reverse do
    acc := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, ← hypFormula h, acc]
  return acc

/-- The hypotheses as a `List (Formula Sig Γ)`. -/
def hypsE : TrM Expr := return (← read).hypsCache

/-- Run with the caches rebuilt for the current variables and hypotheses. -/
def withCaches {α} (k : TrM α) : TrM α := do
  let Γ ← ctxFrom 0
  let Δ ← withReader (fun c => { c with ctxCache := Γ }) hypsList
  withReader (fun c => { c with ctxCache := Γ, hypsCache := Δ }) k

/-- Enter an object variable. -/
def withObj {α} (nm : Name) (ty : Expr) (k : Expr → TrM α) : TrM α := do
  let σ ← (quoteTy ty).run (← read).q
  withLocalDeclD nm ty fun x =>
    withReader (fun c => { c with q := { c.q with objVars := (x.fvarId!, σ) :: c.q.objVars } })
      (withCaches (k x))

/-- Enter a hypothesis. -/
def withHyp {α} (nm : Name) (ty : Expr) (formula : Expr) (k : Expr → TrM α) : TrM α := do
  let d ← depth
  withLocalDeclD nm ty fun h =>
    withReader (fun c => { c with hyps := ⟨h.fvarId!, formula, d⟩ :: c.hyps }) (withCaches (k h))

/-! ### The direct quoter

The same reading as `Classicism/Meta/Quote.lean`, built as an expression with every
implicit argument supplied instead of as syntax to elaborate, which is what makes it fast
enough to run on every subterm of a proof. Returns the term and its object type. -/

partial def quoteE (e : Expr) : TrM (Expr × Expr) := timed "quote" do
  let e ← instantiateMVars e
  let Γ ← ctxE
  let key := (Γ, e)
  if let some r := (← get).quotes[key]? then return r
  checkSystem "derive"
  if (← get).qdepth > 400 then throwError "derive: the quoter loops at{indentExpr e}"
  modify fun s => { s with qdepth := s.qdepth + 1 }
  let r ← try go Γ e finally modify fun s => { s with qdepth := s.qdepth - 1 }
  modify fun s => { s with quotes := s.quotes.insert key r }
  return r
where
  q (e : Expr) : TrM (Expr × Expr) := quoteE e
  ty (e : Expr) : TrM Expr := timed "quote.ty" do (quoteTy e).run (← read).q
  rty (e : Expr) : TrM Expr := timed "quote.ty" do (quoteRTy e).run (← read).q
  /-- A relational operation at the strict type `τ`: as the object constant if `τ` is a
  type parameter, else through the instance, which unfolds at a constructor type. -/
  relOpAt (e τ : Expr) (k : Expr → TrM (Expr × Expr)) : TrM (Expr × Expr) := do
    let ρ ← rty τ
    if isConstructorRTy ρ then
      let e' ← match ← unfoldDefinition? e with
        | some e' => pure e'
        | none => whnfR e
      if e' == e then throwError "derive: the operation {e} at a constructor type does not unfold"
      q e'
    else k ρ
  formula (Γ : Expr) (n : Name) (args : Array Expr) : TrM (Expr × Expr) :=
    return (mkAbbr n Γ args, tyT)
  go (Γ : Expr) (e : Expr) : TrM (Expr × Expr) := do
    match e with
    | .mdata _ b => q b
    | .letE _ _ v b _ => q (b.instantiate1 v)
    | .proj S k b =>
      -- a raw projection of an instance variable: as the projection function applied,
      -- which the cases below read; of anything else, reduced
      if b.isFVar then
        let some e' ← projAsApp S k b | throwError "derive: cannot read the projection {e}"
        q e'
      else
        let e' ← reduceProj e
        if e' == e then throwError "derive: cannot reduce the projection {e}"
        q e'
    | .fvar id =>
      let some i := (← read).q.objVars.findIdx? (·.1 == id)
        | throwError "derive: the variable {e} is not an object variable in scope"
      let σ := (← read).q.objVars[i]!.2
      return (mkTVar Γ σ (← varE i σ), σ)
    | .lam nm d b _ =>
      -- quoted faithfully, with no η-reduction and no β-reduction of redexes: the
      -- derivation's formulas then agree with the quotations of Lean's types
      -- syntactically wherever Lean's kernel did not convert, and a conversion proof is
      -- needed only where it did
      let σ ← ty d
      withObj nm d fun x => do
        let (b', bT) ← q (b.instantiate1 x)
        let ρ ← relOf bT
        return (mkTLam Γ σ ρ b', tRel (tArr σ ρ))
    | .forallE nm d b _ =>
      if ← timed "quote.isProp" (isProp d) then
        let b := betaDeep b
        if b.hasLooseBVars then throwError "derive: a formula depends on a proof: {e}"
        let (d', _) ← q d
        if b.isConstOf ``False then formula Γ ``Classicism.Meta.Term.neg #[d']
        else formula Γ ``Classicism.Meta.Term.imp #[d', (← q b).1]
      else
        let σ ← ty d
        withObj nm d fun x => do
          let (b', _) ← q (b.instantiate1 x)
          return (mkAppN (mkConst ``Classicism.Meta.Term.forall') #[sigE, Γ, σ, b'], tyT)
    | _ =>
      match e.getAppFnArgs with
      | (``And, #[a, b]) => formula Γ ``Classicism.Meta.Term.conj #[(← q a).1, (← q b).1]
      | (``Or, #[a, b]) => formula Γ ``Classicism.Meta.Term.disj #[(← q a).1, (← q b).1]
      | (``Not, #[a]) => formula Γ ``Classicism.Meta.Term.neg #[(← q a).1]
      | (``Classicism.imp, #[a, b]) => formula Γ ``Classicism.Meta.Term.imp #[(← q a).1, (← q b).1]
      | (``Classicism.iff, #[a, b]) => formula Γ ``Classicism.Meta.Term.iff #[(← q a).1, (← q b).1]
      | (``True, #[]) => formula Γ ``Classicism.Meta.Term.top #[]
      | (``False, #[]) => formula Γ ``Classicism.Meta.Term.bot #[]
      | (``Classicism.Box, #[a]) => formula Γ ``Classicism.Meta.Term.box #[(← q a).1]
      | (``Classicism.Dia, #[a]) => formula Γ ``Classicism.Meta.Term.dia #[(← q a).1]
      | (``Iff, #[a, b]) => formula Γ ``Classicism.Meta.Term.iff #[(← q a).1, (← q b).1]
      | (``Eq, #[α, a, b]) =>
        let σ ← ty α
        return (mkAppN (mkConst ``Classicism.Meta.Term.eq') #[sigE, Γ, σ, (← q a).1, (← q b).1], tyT)
      | (``Exists, #[α, F]) =>
        let σ ← ty α
        match F with
        | .lam nm d b _ =>
          withObj nm d fun x => do
            let (b', _) ← q (b.instantiate1 x)
            return (mkAppN (mkConst ``Classicism.Meta.Term.exists') #[sigE, Γ, σ, b'], tyT)
        | _ =>
          let ex := mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ]
          return (mkTApp Γ (tRel (tArr σ rtE)) rtE ex (← q F).1, tyT)
      -- a relational operation: at a type parameter, the object constant `andR τ'` applied;
      -- at a constructor type, the instance unfolds and the operation is read through it
      | (``Classicism.Rel.constP, #[τ, _, p]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.constR ρ Γ #[(← q p).1], tRel ρ)
      | (``Classicism.Rel.neg, #[τ, _, X]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.negR ρ Γ #[(← q X).1], tRel ρ)
      | (``Classicism.Rel.and, #[τ, _, X, Y]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.andR ρ Γ #[(← q X).1, (← q Y).1], tRel ρ)
      | (``Classicism.Rel.or, #[τ, _, X, Y]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.orR ρ Γ #[(← q X).1, (← q Y).1], tRel ρ)
      | (``Classicism.Rel.coext, #[τ, _, X, Y]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.coextR ρ Γ #[(← q X).1, (← q Y).1], tyT)
      | (``Classicism.Rel.boxAt, #[τ, _, X]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.boxR ρ Γ #[(← q X).1], tRel ρ)
      | (``Classicism.Rel.incl, #[τ, _, X, Y]) =>
        relOpAt e τ fun ρ => return (mkRel ``Classicism.Meta.Term.inclR ρ Γ #[(← q X).1, (← q Y).1], tyT)
      | (``Eq, args) =>
        -- `Eq α`, `Eq α a`: identity unapplied or partially applied, as η-reduction of
        -- `fun z => a = z` leaves it
        let σ ← ty args[0]!
        let mut acc := mkAppN (mkConst ``Classicism.Meta.Term.eq) #[sigE, Γ, σ]
        let mut T := tRel (tArr σ (tArr σ rtE))
        for a in args.extract 1 args.size do
          let (σ', ρ) ← splitArrow T
          acc := mkTApp Γ σ' ρ acc (← q a).1
          T := tRel ρ
        return (acc, T)
      | (``Exists, #[α]) =>
        let σ ← ty α
        return (mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ], tRel (tArr (tRel (tArr σ rtE)) rtE))
      | (``And, args) | (``Or, args) | (``Not, args) =>
        -- a connective unapplied or partially applied, as the instance fields at `Prop`
        -- leave it: the constant, then the applications
        let c := e.getAppFn.constName!
        let base := if c == ``And then ``Classicism.Meta.Term.and
          else if c == ``Or then ``Classicism.Meta.Term.or else ``Classicism.Meta.Term.not
        let mut acc := mkAppN (mkConst base) #[sigE, Γ]
        let mut T := if c == ``Not then tRel (tArr tyT rtE) else tRel (tArr tyT (tArr tyT rtE))
        for a in args do
          let (σ, ρ) ← splitArrow T
          acc := mkTApp Γ σ ρ acc (← q a).1
          T := tRel ρ
        return (acc, T)
      | _ =>
        let f := e.getAppFn
        let args := e.getAppArgs
        -- a relational operation partially applied, as `simp`'s congruence lemmas leave
        -- it (`congrArg _ (constP τ)`): η-expand it, and read the abstraction
        if let some n := f.constName? then
          if let some k := relOpArity? n then
            if args.size < k then
              let e' ← forallTelescopeReducing (← inferType e) fun xs _ =>
                mkLambdaFVars xs (mkAppN e xs)
              return ← q e'
        if let .proj S k b := f then
          -- an applied raw projection: the head as above, then the arguments
          if b.isFVar then
            let some f' ← projAsApp S k b | throwError "derive: cannot read the projection {f}"
            return ← q (mkAppN f' args)
          else
            let f' ← reduceProj f
            if f' == f then throwError "derive: cannot reduce the projection {f}"
            return ← q (mkAppN f' args)
        if f.isFVar then
          let mut (acc, T) ← q f
          for a in args do
            let (σ, ρ) ← splitArrow T
            let (a', _) ← q a
            acc := mkTApp Γ σ ρ acc a'
            T := tRel ρ
          return (acc, T)
        if f.isLambda then
          -- a redex is quoted as a redex
          let mut (acc, T) ← q f
          for a in args do
            let (σ, ρ) ← splitArrow T
            let (a', _) ← q a
            acc := mkTApp Γ σ ρ acc a'
            T := tRel ρ
          return (acc, T)
        match ← timed "quote.unfold" (unfoldDefinition? e) with
        | some e' =>
          if let .proj _ _ b := e'.getAppFn then
            if b.isFVar then throwError "derive: no reading of the field {f} of an instance variable"
          q e'
        | none =>
          let e' ← timed "quote.unfold" (whnfCore e)
          if e' != e then q e'
          else
            let e'' ← timed "quote.unfold" (whnfR e)
            if e'' != e then q e''
            else throwError "derive: cannot read {e} as an object term"

/-- Quote a Lean proposition as a formula in the current context. -/
def quoteF (e : Expr) : TrM Expr := return (← quoteE e).1

/-- Quote a Lean object as a term in the current context. -/
def quoteT (e : Expr) : TrM Expr := return (← quoteE e).1

/-! ### Rules, built directly -/

/-- A rule of `Derivable`, with every argument given: the parameters `Sig` and `Ax`, then
the constructor's own in order. -/
def rule (n : Name) (args : Array Expr) : TrM Expr := timed "rule" do
  let r := mkAppN (mkConst n) (#[sigE, ← curAx] ++ args)
  if Classicism.Meta.Translate.check.get (← getOptions) then
    try Meta.check r catch ex =>
      throwError "derive: internal error building {n}:\n{ex.toMessageData}"
  return r

/-! ### Conversion

For the check that two formulas convert, before the kernel is asked to, the translator
keeps an **untyped shadow** of the object syntax, `Tm`, into which object-term expressions
are read with `whnf` at each node, and in which β- and η-normalization is a few lines.
Two formulas whose shadows normalize alike are then joined by an explicit conversion
built from the normalization, below. -/


/-- Normalize a type expression for comparison: unfold abbreviations such as `Ty.t` at
every level. -/
partial def normTy (e : Expr) : MetaM Expr := do
  let e ← whnf (← instantiateMVars e)
  match e.getAppFnArgs with
  | (``Classicism.Meta.Ty.rel, #[ρ]) => return mkApp (mkConst ``Classicism.Meta.Ty.rel) (← normTy ρ)
  | (``Classicism.Meta.RTy.arr, #[σ, ρ]) =>
    return mkApp2 (mkConst ``Classicism.Meta.RTy.arr) (← normTy σ) (← normTy ρ)
  | _ => return e

/-- Read an object-term expression as a shadow term. Anything that is not a constructor
of the syntax after `whnf`, such as a relational operation at a type parameter, is opaque. -/
partial def shadow (t : Expr) : TrM Tm := do
  let t ← instantiateMVars t
  if let some r := (← get).shadows[t]? then return r
  let r ← go t
  modify fun s => { s with shadows := s.shadows.insert t r }
  return r
where
  go (t : Expr) : TrM Tm := do
    -- a substitution is done on the shadow, not by evaluating the syntax's
    match t.getAppFn.constName?, t.getAppArgs with
    | some ``Classicism.Meta.Term.instantiate, #[_, _, _, _, b, a] =>
      return Tm.subst 0 (← shadow a) (← shadow b)
    | some ``Classicism.Meta.Term.weaken, #[_, _, _, _, a] => return Tm.shift 1 0 (← shadow a)
    | some ``Classicism.Meta.Term.close, #[_, _, _, a] => shadow a
    | _, _ =>
    let t ← whnf t
    match t.getAppFn.constName?, t.getAppArgs with
    | some ``Classicism.Meta.Term.app, #[_, _, σ, ρ, f, a] =>
      return .app (← normTy' σ) (← normTy' ρ) (← shadow f) (← shadow a)
    | some ``Classicism.Meta.Term.lam, #[_, _, σ, ρ, b] =>
      return .lam (← normTy' σ) (← normTy' ρ) (← shadow b)
    | some ``Classicism.Meta.Term.var, #[_, _, _, v] => return .var (← varIndex v)
    | some ``Classicism.Meta.Term.and, _ => return .const ``Classicism.Meta.Term.and tyT
    | some ``Classicism.Meta.Term.or, _ => return .const ``Classicism.Meta.Term.or tyT
    | some ``Classicism.Meta.Term.not, _ => return .const ``Classicism.Meta.Term.not tyT
    | some ``Classicism.Meta.Term.all, #[_, _, σ] => return .const ``Classicism.Meta.Term.all (← normTy' σ)
    | some ``Classicism.Meta.Term.ex, #[_, _, σ] => return .const ``Classicism.Meta.Term.ex (← normTy' σ)
    | some ``Classicism.Meta.Term.eq, #[_, _, σ] => return .const ``Classicism.Meta.Term.eq (← normTy' σ)
    | some ``Classicism.Meta.Term.const, #[_, _, c] => return .const ``Classicism.Meta.Term.const (← instantiateMVars c)
    | some n, #[Γ, _, ρ] =>
      -- a type-subscripted operation `op Sig Γ ρ`: a constant, at its type
      if Tm.isRelOp n then return .const n (← normTy' ρ)
      return .opaque Γ (← instantiateMVars t)
    | _, _ =>
      let ty ← whnf (← inferType t)
      let Γ := ty.getAppArgs[1]?.getD (Lean.mkConst ``List.nil)
      return .opaque Γ (← instantiateMVars t)
  /-- `normTy`, memoized. -/
  normTy' (e : Expr) : TrM Expr := do
    let e ← instantiateMVars e
    if let some r := (← get).normTys[e]? then return r
    let r ← normTy e
    modify fun s => { s with normTys := s.normTys.insert e r }
    return r
  varIndex (v : Expr) : TrM Nat := do
    let v ← whnf v
    match v.getAppFn.constName?, v.getAppArgs with
    | some ``Classicism.Meta.Var.zero, _ => pure 0
    | some ``Classicism.Meta.Var.succ, args => return (← varIndex args.back!) + 1
    | _, _ => throwError "derive: not a variable: {v}"

/-- Unfold every type-subscripted operation at a constructor type in an object term,
recursively, with a proof of the conversion: `Conv.delta rfl` at each, under `app` and
`lam` congruences. Returns the term unchanged and no proof if there is nothing to unfold.
The kernel evaluates `Term.unfoldR` only at constructor types here, where it reduces. -/
partial def unfoldConv (Γ : Expr) (t : Expr) : TrM (Expr × Option Expr) := do
  let t₀ ← instantiateMVars t
  -- the abbreviations `eq'`, `conj`, `forall'` and the rest unfold to the constructors
  let t ← whnfR t₀
  match t.getAppFn.constName?, t.getAppArgs with
  | some ``Classicism.Meta.Term.app, #[_, _, σ, ρ, f, a] =>
    let (f', pf) ← unfoldConv Γ f
    let (a', pa) ← unfoldConv Γ a
    if pf.isNone && pa.isNone then return (t₀, none)
    let pf := pf.getD (mkAppN (mkConst ``Classicism.Meta.Conv.refl) #[sigE, Γ, tRel (tArr σ ρ), f])
    let pa := pa.getD (mkAppN (mkConst ``Classicism.Meta.Conv.refl) #[sigE, Γ, σ, a])
    return (mkTApp Γ σ ρ f' a',
      some (mkAppN (mkConst ``Classicism.Meta.Conv.app_congr) #[sigE, Γ, σ, ρ, f, f', a, a', pf, pa]))
  | some ``Classicism.Meta.Term.lam, #[_, _, σ, ρ, b] =>
    let Γ' := mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, Γ]
    let (b', pb) ← unfoldConv Γ' b
    let some pb := pb | return (t₀, none)
    return (mkTLam Γ σ ρ b',
      some (mkAppN (mkConst ``Classicism.Meta.Conv.lam_congr) #[sigE, Γ, σ, ρ, b, b', pb]))
  | some n, #[_, _, ρ] =>
    unless Tm.isRelOp n do return (t₀, none)
    let ρ ← instantiateMVars ρ
    unless isConstructorRTy (← whnf ρ) do return (t₀, none)
    -- the unfolding, by evaluating `unfoldR` at this constructor type
    let T := relOpType n ρ
    let u ← whnf (mkAppN (mkConst ``Classicism.Meta.Term.unfoldR) #[sigE, Γ, T, t])
    let some (_, u) := u.app2? ``Option.some
      | throwError "derive: {t} did not unfold, giving{indentExpr u}"
    let optTy := mkApp (mkConst ``Option [Level.zero]) (mkApp3 (mkConst ``Classicism.Meta.Term) sigE Γ T)
    let h := mkAppN (mkConst ``Eq.refl [Level.one]) #[optTy, mkApp2 (mkConst ``Option.some [Level.zero]) (mkApp3 (mkConst ``Classicism.Meta.Term) sigE Γ T) u]
    let p₁ := mkAppN (mkConst ``Classicism.Meta.Conv.delta) #[sigE, Γ, T, t, u, h]
    -- the unfolding mentions the operation at the smaller type, which may unfold further
    let (u', pu) ← unfoldConv Γ u
    match pu with
    | none => return (u, some p₁)
    | some pu => return (u', some (mkAppN (mkConst ``Classicism.Meta.Conv.trans) #[sigE, Γ, T, t, u, u', p₁, pu]))
  | _, _ => return (t₀, none)

/-! ### Shadows written back

A shadow carries the types of its binders and applications so that it can be written
back as syntax, `toTerm`: the induction on the type needs the unfolding of an operation
as a term, and the step case's statement is assembled from shadows. Two other designs of
the conversion certificate were tried and measured slower than `Conv.of_nf` on a whole
formula: explicit β- and η-steps for every pass, which write out every intermediate term
and cost more in the kernel and the elaborator both; and `Conv.of_nf` only at the
subterms where two shadows differ, joined by congruence, which leaves the kernel to
compare the original term with the shadow written back, two shapes it unfolds lazily
against each other, its slowest path. -/

/-- The types of a context expression, innermost first: a literal `List.cons` chain. -/
partial def ctxTypes (Γ : Expr) : List Expr :=
  match Γ.app3? ``List.cons with
  | some (_, σ, Γ') => σ :: ctxTypes Γ'
  | none => []

/-- The context expression dropping `i` innermost variables. -/
partial def ctxDrop (Γ : Expr) (i : Nat) : Expr :=
  if i == 0 then Γ else
  match Γ.app3? ``List.cons with
  | some (_, _, Γ') => ctxDrop Γ' (i - 1)
  | none => Γ

/-- The variable at index `i` in the context `Γ`, as `Var.succ^i Var.zero`, and its type. -/
def varIn (Γ : Expr) (i : Nat) : Expr × Expr := Id.run do
  let tys := (ctxTypes Γ).toArray
  let σ := tys[i]!
  let mut v := mkAppN (mkConst ``Classicism.Meta.Var.zero) #[ctxDrop Γ (i + 1), σ]
  for j in [0:i] do
    let j := i - 1 - j
    v := mkAppN (mkConst ``Classicism.Meta.Var.succ) #[ctxDrop Γ (j + 1), σ, tys[j]!, v]
  return (v, σ)

/-- A constant of the syntax, in context. -/
def constIn (Γ : Expr) (n : Name) (ty : Expr) : Expr :=
  if n == ``Classicism.Meta.Term.and || n == ``Classicism.Meta.Term.or || n == ``Classicism.Meta.Term.not then
    mkAppN (mkConst n) #[sigE, Γ]
  else mkAppN (mkConst n) #[sigE, Γ, ty]

/-- A shadow written back as syntax, in the context `Γ`. -/
partial def toTerm (Γ : Expr) : Tm → TrM Expr
  | .var i => do
    modify fun s => { s with timing := s.timing.insert "toTerm.var" (s.timing.getD "toTerm.var" 0 + 1) }
    let (v, σ) := varIn Γ i
    return mkTVar Γ σ v
  | .app σ ρ f a => return mkTApp Γ σ ρ (← toTerm Γ f) (← toTerm Γ a)
  | .lam σ ρ b => return mkTLam Γ σ ρ (← toTerm (mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, Γ]) b)
  | .const n ty => return constIn Γ n ty
  | .opaque Γ' e => do
    unless Γ' == Γ do
      throwError "derive: an unreadable subterm{indentExpr e}\nmoved under a binder by a conversion"
    return e

/-- The type of a shadow term whose context is `Γ`. -/
partial def typeOf (Γ : Expr) : Tm → TrM Expr
  | .var i => return (varIn Γ i).2
  | .app _ ρ _ _ => return tRel ρ
  | .lam σ ρ _ => return tRel (tArr σ ρ)
  | .const n ty =>
    if n == ``Classicism.Meta.Term.and || n == ``Classicism.Meta.Term.or then return tRel (tArr tyT (tArr tyT rtE))
    else if n == ``Classicism.Meta.Term.not then return tRel (tArr tyT rtE)
    else if n == ``Classicism.Meta.Term.all || n == ``Classicism.Meta.Term.ex then return tRel (tArr (tRel (tArr ty rtE)) rtE)
    else if n == ``Classicism.Meta.Term.eq then return tRel (tArr ty (tArr ty rtE))
    else if Tm.isRelOp n then return relOpType n ty
    else throwError "derive: the type of the constant {n} is unknown"
  | .opaque _ e => do
    let T ← whnf (← inferType e)
    return T.getAppArgs[2]!

def convRefl (Γ T a : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Conv.refl) #[sigE, Γ, T, a]
def convTrans (Γ T a b c p q : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Conv.trans) #[sigE, Γ, T, a, b, c, p, q]
def convSymm (Γ T a b p : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Conv.symm) #[sigE, Γ, T, a, b, p]

/-- The normal form of a shadow and the passes it took, memoized. -/
def normalizeTm (t : Tm) : TrM (Tm × Nat) := do
  if let some r := (← get).nfMemo[t]? then return r
  let some r := t.normalize
    | throwError "derive: a shadow did not normalize in 500 passes"
  modify fun s => { s with nfMemo := s.nfMemo.insert t r }
  return r

/-- The normalized shadow of an object term and the passes it took, memoized. -/
def shadowNf (t : Expr) : TrM (Tm × Nat) := timed "nf" do
  let t ← instantiateMVars t
  if let some r := (← get).nfs[t]? then return r
  let sh ← timed "nf.shadow" (shadow t)
  let r ← timed "nf.normalize" (normalizeTm sh)
  modify fun s => { s with nfs := s.nfs.insert t r }
  return r

/-- Is the root of the shadow stable under normalization: not an application whose
function normalizes to an abstraction, nor an abstraction whose body normalizes to an
η-redex? At a stable root, normal forms agree exactly when those of the children do. -/
def rootStable : Tm → TrM Bool
  | .app _ _ f _ => do
    let (f', _) ← normalizeTm f
    return !(f' matches .lam _ _ _)
  | .lam σ ρ b => do
    let (b', _) ← normalizeTm b
    return (Tm.etaRed (.lam σ ρ b') matches .lam _ _ _)
  | _ => return true

/-- A proof that two shadows in context `Γ`, which normalize alike, convert: descending
by congruence while both roots are stable, and where they differ, `Conv.of_nf` on the
subterms, so that the kernel evaluates the normalizer only on what differs. `none` if the
two are the same. -/
partial def diffConv (Γ : Expr) (g e : Tm) : TrM (Option Expr) := do
  if g == e then return none
  match g, e with
  | .app σ ρ f a, .app σ' ρ' f' a' =>
    if σ == σ' && ρ == ρ' && (← rootStable g) && (← rootStable e) then
      let pf ← diffConv Γ f f'
      let pa ← diffConv Γ a a'
      if pf.isNone && pa.isNone then return none
      let fE ← toTerm Γ f; let aE ← toTerm Γ a
      let pf := pf.getD (convRefl Γ (tRel (tArr σ ρ)) fE)
      let pa := pa.getD (convRefl Γ σ aE)
      return some (mkAppN (mkConst ``Classicism.Meta.Conv.app_congr)
        #[sigE, Γ, σ, ρ, fE, ← toTerm Γ f', aE, ← toTerm Γ a', pf, pa])
    else byNf
  | .lam σ ρ b, .lam σ' ρ' b' =>
    if σ == σ' && ρ == ρ' && (← rootStable g) && (← rootStable e) then
      let Γ' := mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, Γ]
      let some pb ← diffConv Γ' b b' | return none
      return some (mkAppN (mkConst ``Classicism.Meta.Conv.lam_congr)
        #[sigE, Γ, σ, ρ, ← toTerm Γ' b, ← toTerm Γ' b', pb])
    else byNf
  | _, _ => byNf
where
  byNf : TrM (Option Expr) := do
    let (gn, kg) ← normalizeTm g
    let (en, ke) ← normalizeTm e
    unless gn == en do
      throwError "derive: internal error, subterms that do not convert: {repr g} and {repr e}"
    let T ← typeOf Γ g
    let gE ← toTerm Γ g; let eE ← toTerm Γ e
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
      let N ← toTerm Γ gn
      let p₁ := mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_left) #[sigE, Γ, T, mkRawNatLit kg, gE, N, refl N]
      let p₂ := mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_right) #[sigE, Γ, T, mkRawNatLit ke, N, eE, refl N]
      return some (convTrans Γ T gE N eE p₁ p₂)

/-- An object-term expression as its canonical tree, the shadow written back, with a proof
of the conversion when the expression is not already that tree: a form such as
`b.instantiate a` or `close p`, or one using an abbreviation, which the kernel evaluates
to the tree. The proof is `Conv.of_nf_left 0`, so that the kernel has the tree as written
and the form to evaluate. -/
def canon (t : Expr) : TrM (Expr × Option Expr) := do
  let Γ ← ctxE
  let T ← toTerm Γ (← shadow t)
  if T == t then return (T, none)
  let termTy := mkApp3 (mkConst ``Classicism.Meta.Term) sigE Γ tyT
  let h := mkAppN (mkConst ``Eq.refl [Level.one]) #[termTy, T]
  return (T, some (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_left) #[sigE, Γ, tyT, mkRawNatLit 0, t, T, h]))

/-- Use a derivation of `got` as one of `exp`: directly if they are the same, else through
`conv` with `Conv.of_nf`, after checking that their shadows normalize alike. The kernel
is only ever given one side to evaluate against a tree as written: each side is first
bridged to its canonical tree, and the normalizer runs between the two trees. Comparing
two forms it has to unfold lazily against each other, `b.instantiate a` with
`b'.instantiate a'`, is the kernel's slowest path, and was the cost of a first version
that let it compare the forms directly. -/
def coerce (d got exp : Expr) : TrM Expr := do
  let got ← instantiateMVars got
  let exp ← instantiateMVars exp
  if got == exp then return d
  let (g', _) ← shadowNf got
  let (e', _) ← shadowNf exp
  unless g' == e' do
    throwError "derive: the derivation proves{indentExpr got}\nbut{indentExpr exp}\nwas expected, and the two do not convert; normal forms {repr g'} and {repr e'}"
  let Γ ← ctxE
  let (gT, bg) ← canon got
  let (eT, be) ← canon exp
  -- between the two trees: the local certificate, `of_nf` only where they differ
  let mid ← timed "diff" (diffConv Γ (← shadow got) (← shadow exp))
  if mid.isNone then
    modify fun s => { s with timing := s.timing.insert "defeq" (s.timing.getD "defeq" 0 + 1) }
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
  rule ``Classicism.Meta.Derivable.conv #[Γ, ← hypsE, got, exp, d, c]

/-! ### The interpretation -/

/-- The membership proof for the hypothesis at index `i`: `tail` past the hypotheses in
front of it, then `head`. -/
def memProof (i : Nat) : TrM Expr := do
  let Γ ← ctxE
  let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
  let formulas ← (← read).hyps.mapM hypFormula
  let target := formulas[i]!
  let listE (fs : List Expr) : Expr := Id.run do
    let mut acc := mkApp (mkConst ``List.nil [Level.zero]) fty
    for g in fs.reverse do acc := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, g, acc]
    return acc
  let rec go (j : Nat) (fs : List Expr) : TrM Expr := do
    match fs with
    | [] => throwError "derive: internal error in memProof"
    | f :: rest =>
      if j == i then return mkAppN (mkConst ``List.Mem.head [Level.zero]) #[fty, target, listE rest]
      else return mkAppN (mkConst ``List.Mem.tail [Level.zero]) #[fty, target, f, listE rest, ← go (j + 1) rest]
  go 0 formulas

/-- Is the argument a type or an instance? -/
def isParam (a : Expr) : MetaM Bool := do
  let t ← whnf (← inferType a)
  if let .sort l := t then return !l.isZero
  return (← isClass? t).isSome

/-- A proof that the logical axiom is in the current axiom set: `Eq.refl` for
`C.axioms`, which is `Logical`, and `And.intro` once per logical depth. -/
def logicalMember (a : Expr) : TrM Expr := do
  let c ← read
  unless c.axIsC do throwError "derive: `e_exists` used, but the theorem was to be derived in C⁻"
  let base ← mkEqRefl a
  let mut pf := base
  for _ in [0:c.logicalDepth] do
    pf ← mkAppM ``And.intro #[pf, base]
  return pf

/-- Lift a theorem of the run's axiom set into the current one, inside the premises of a
Subst: `mono` along the inclusion of the set in its logical part. -/
def liftLogical (thm : Expr) : TrM Expr := do
  let c ← read
  if c.logicalDepth == 0 then return thm
  let sentenceTy := mkApp (mkConst ``Classicism.Meta.Sentence) sigE
  let hA ← withLocalDeclD `a sentenceTy fun a => withLocalDeclD `h (mkApp c.ax a) fun h => do
    let mut pf := h
    if c.axIsC then
      for _ in [0:c.logicalDepth] do
        pf ← mkAppM ``And.intro #[pf, h]
    else
      pf ← mkAppOptM ``False.elim #[mkApp (← curAx) a, h]
    mkLambdaFVars #[a, h] pf
  mkAppM ``Classicism.Meta.Derivable.mono #[hA, thm]

/-- The mirror classes whose laws are held as fields, with their instances at `Prop` and
at `σ → τ`. A law cited at a type *parameter* is not an axiom: it is derived once for
every object type, by induction on the type, the `Prop` instance's proof the base case
and the arrow instance's the step, with the law at the smaller type as hypothesis. -/
def inductionInstances : Name → Option (Name × Name)
  | ``Classicism.Rel => some (``Classicism.instRelProp, ``Classicism.instRelArrow)
  | ``Classicism.Order => some (``Classicism.instOrderProp, ``Classicism.instOrderArrow)
  | ``Classicism.Pointwise => some (``Classicism.instPointwiseProp, ``Classicism.instPointwiseArrow)
  | _ => none

/-- `Term.imp A B` and friends, as expressions in context. -/
def impE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.imp Γ #[A, B]
def negE (Γ A : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.neg Γ #[A]
def conjE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.conj Γ #[A, B]
def disjE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.disj Γ #[A, B]
def iffE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.iff Γ #[A, B]
def botE (Γ : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.bot Γ #[]
def eqE (Γ σ a b : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.eq') #[sigE, Γ, σ, a, b]

/-- The arity at which a core constant is one rule; applied to more arguments, the rest
are fed to the result. -/
def coreArity : Name → Option Nat
  | ``id => some 2 | ``Eq.refl => some 2 | ``rfl => some 2
  | ``Eq.symm => some 4 | ``Eq.trans => some 6 | ``congrArg => some 6 | ``congrFun => some 6
  | ``Eq.mpr => some 4 | ``Eq.mp => some 4 | ``Eq.subst => some 6
  | ``And.intro => some 4 | ``And.left => some 3 | ``And.right => some 3
  | ``Or.inl => some 3 | ``Or.inr => some 3 | ``Or.elim => some 6
  | ``absurd => some 4 | ``False.elim => some 2
  | ``Iff.intro => some 4 | ``Iff.mp => some 3 | ``Iff.mpr => some 3
  | ``Iff.refl => some 1 | ``Iff.rfl => some 1 | ``Iff.symm => some 3 | ``Iff.trans => some 5
  | ``Exists.intro => some 4 | ``Exists.elim => some 5
  | ``propext => some 3 | ``funext => some 5
  | ``Classicism.em => some 1 | ``True.intro => some 0 | ``trivial => some 0
  | _ => none

/-- Core theorems the translator unfolds at their use, rather than cites: the ones `simp`
leaves in a proof term. Each body is a few nodes of `propext`, `funext`, `Eq.rec` and
`Iff.intro` applied to the theorem's arguments, so after β-reduction the rules above take
over; `eq_true h` becomes `propext ⟨_, fun _ => h⟩`, Subst with `h` closed, and
`forall_congr h` becomes `funext h` under Leibniz's Law. The gate has already checked
that the hypothesis argument of each is closed (`Check.gatedRules`). -/
def coreUnfolded : List Name :=
  [``of_eq_true, ``of_eq_false, ``eq_true, ``eq_false, ``eq_self, ``congr, ``congrFun',
   ``forall_congr]

mutual

/-- The derivation of a strict proof term `t : A`: the formula it proves, and the proof of
`Derivable Ax Δ` of it. -/
partial def interp (t : Expr) : TrM (Expr × Expr) := do
  let t := (← instantiateMVars t).consumeMData
  checkSystem "derive"
  let key := (← ctxE, ← hypsE, t)
  if let some r := (← get).interps[key]? then return r
  let n := (← get).interps.size
  if n % 500 == 0 then
    trace s!"    interp: {n} proof nodes, {(← get).quotes.size} quotations, {(← get).nfs.size} normal forms, {(← get).shadows.size} shadows"
  let r ← interpCore t
  modify fun s => { s with interps := s.interps.insert key r }
  return r

partial def interpCore (t : Expr) : TrM (Expr × Expr) := do
  match t with
  | .letE _ _ v b _ => interp (b.instantiate1 v)
  | .mdata _ b => interp b
  | .fvar id =>
    let hs := (← read).hyps
    let some i := hs.findIdx? (·.fvar == id)
      | throwError "derive: {t} is not a hypothesis in scope"
    let f ← hypFormula hs[i]!
    let d ← rule ``Classicism.Meta.Derivable.hyp #[← ctxE, ← hypsE, f, ← memProof i]
    return (f, d)
  | .lam nm d b _ =>
    if ← isProp d then
      let H ← quoteF d
      let Γ ← ctxE
      let Δ ← hypsE
      withHyp nm d H fun h => do
        let body := b.instantiate1 h
        let (B, db) ← interp body
        let bodyTy ← whnfR (← inferType body)
        if bodyTy.isConstOf ``False then
          let db ← coerce db B (botE Γ)
          let everything := mkAbbr ``Classicism.Meta.Term.forall' Γ #[tyT,
            mkTVar (mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, tyT, Γ]) tyT
              (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, tyT])]
          let Δ' := mkAppN (mkConst ``List.cons [Level.zero]) #[mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ, H, Δ]
          let h₁ ← rule ``Classicism.Meta.Derivable.andE₁ #[Γ, Δ', everything, negE Γ everything, db]
          let h₂ ← rule ``Classicism.Meta.Derivable.andE₂ #[Γ, Δ', everything, negE Γ everything, db]
          let d ← rule ``Classicism.Meta.Derivable.notI #[Γ, Δ, H, everything, h₁, h₂]
          return (negE Γ H, d)
        let d ← rule ``Classicism.Meta.Derivable.impI #[Γ, Δ, H, B, db]
        return (impE Γ H B, d)
    else
      if ← isParam' d then
        throwError "derive: a proof abstracts over a type or an instance inside a formula"
      let Γ ← ctxE
      let Δ ← hypsE
      let σ ← (quoteTy d).run (← read).q
      withObj nm d fun x => do
        let (B, db) ← interp (b.instantiate1 x)
        let F := mkAbbr ``Classicism.Meta.Term.forall' Γ #[σ, B]
        let d ← rule ``Classicism.Meta.Derivable.allI #[Γ, Δ, σ, B, db]
        return (F, d)
  | .proj S i e =>
    let ty ← whnf (← inferType e)
    match S, i, ty.getAppFnArgs with
    | ``And, 0, (_, #[a, b]) => interp (mkApp3 (mkConst ``And.left) a b e)
    | ``And, 1, (_, #[a, b]) => interp (mkApp3 (mkConst ``And.right) a b e)
    | ``Iff, 0, (_, #[a, b]) => interp (mkApp3 (mkConst ``Iff.mp) a b e)
    | ``Iff, 1, (_, #[a, b]) => interp (mkApp3 (mkConst ``Iff.mpr) a b e)
    | _, _, _ =>
      -- a field of a class instance: reduce the projection of the constructor
      let t' ← whnfCore t
      if t' != t then interp t'
      else
        let t'' ← whnfR t
        if t'' != t then interp t''
        else if let .fvar fid := e then
          -- a law of a mirror class at a type parameter: the induction hypothesis if
          -- this is the law being derived by induction, else the law derived for every
          -- object type, at this one
          if let some (_, _, ih) := (← read).ihs.find? (fun (f, j, _) => f == fid && j == i) then
            citeTheorem t ih
          else if (inductionInstances S).isSome then
            let τ := ty.getAppArgs[0]!
            let some (_, _, tv) := (← read).q.tyVars.find? (·.1 == τ.fvarId!)
              | throwError "derive: the type {τ} of the instance {e} is not a metalogical type parameter"
            let name ← ensureFieldInduction S i
            citeTheorem t (mkApp (mkConst name) tv)
          else throwError "derive: projection {i} of {S} is not handled, of{indentExpr e}\nof type{indentExpr ty}"
        else throwError "derive: projection {i} of {S} is not handled, of{indentExpr e}\nof type{indentExpr ty}"
  | .app .. | .const .. => interpApp t.getAppFn t.getAppArgs
  | _ => throwError "derive: proof term of an unexpected form: {t}"

partial def isParam' (d : Expr) : TrM Bool := do
  let d ← whnf d
  if let .sort l := d then return !l.isZero
  return (← isClass? d).isSome

/-- A derivation of a branch `f : A → C` of a case analysis, as `(A :: Δ) ⊢ C`. -/
partial def branch (f : Expr) (A : Expr) (AF CF : Expr) : TrM Expr := do
  match f with
  | .lam nm _ b _ =>
    withHyp nm A AF fun h => do
      let (got, d) ← interp (b.instantiate1 h)
      coerce d got CF
  | _ =>
    -- a branch that is not an abstraction (`Or.inl`, a lemma): η-expand it
    withHyp `h A AF fun h => do
      let (got, d) ← interp (mkApp f h)
      coerce d got CF

partial def interpApp (f : Expr) (args : Array Expr) : TrM (Expr × Expr) := do
  let t := mkAppN f args
  let Γ ← ctxE
  let Δ ← hypsE
  if let .const c ls := f then
    if let some k := coreArity c then
      if args.size > k then
        let (F, d) ← interpApp f (args.extract 0 k)
        return ← feed (mkAppN f (args.extract 0 k)) F d (args.extract k args.size)
    match c, args with
    | ``id, #[_, a] => return ← interp a
    | ``Eq.refl, #[_, a] | ``rfl, #[_, a] =>
      let (a', σ) ← quoteE a
      return (eqE Γ σ a' a', ← rule ``Classicism.Meta.Derivable.refl #[Γ, Δ, σ, a'])
    | ``Eq.symm, #[_, a, b, h] =>
      let (got, d) ← interp h
      let (a', σ) ← quoteE a; let (b', _) ← quoteE b
      let d ← coerce d got (eqE Γ σ a' b')
      return (eqE Γ σ b' a', ← rule ``Classicism.Meta.Derivable.eqSymm #[Γ, Δ, σ, a', b', d])
    | ``Eq.trans, #[_, a, b, c', h₁, h₂] =>
      let (g₁, d₁) ← interp h₁
      let (g₂, d₂) ← interp h₂
      let (a', σ) ← quoteE a; let (b', _) ← quoteE b; let (c'', _) ← quoteE c'
      let d₁ ← coerce d₁ g₁ (eqE Γ σ a' b')
      let d₂ ← coerce d₂ g₂ (eqE Γ σ b' c'')
      return (eqE Γ σ a' c'', ← rule ``Classicism.Meta.Derivable.eqTrans #[Γ, Δ, σ, a', b', c'', d₁, d₂])
    | ``Trans.trans, _ =>
      if args.size ≥ 12 && args[6]!.isAppOf ``instTransEq then
        return ← interpApp (mkConst ``Eq.trans ls.tail!) (#[args[0]!] ++ args.extract 7 args.size)
      throwError "derive: `Trans.trans` not at an equation"
    | ``congrArg, #[_, _, a₁, a₂, fn, h] =>
      let (got, d) ← interp h
      let (a₁', σ) ← quoteE a₁; let (a₂', _) ← quoteE a₂
      let d ← coerce d got (eqE Γ σ a₁' a₂')
      let (fn', fT) ← quoteE fn
      let (_, ρ) ← splitArrow fT
      if let some B := lamBody? fn' then
        -- a lambda: conclude with the substitution, as Lean's type has it
        let l := instE Γ σ (tRel ρ) B a₁'
        let r := instE Γ σ (tRel ρ) B a₂'
        return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongrβ #[Γ, Δ, σ, ρ, B, a₁', a₂', d])
      let l := mkTApp Γ σ ρ fn' a₁'
      let r := mkTApp Γ σ ρ fn' a₂'
      return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongr #[Γ, Δ, σ, ρ, fn', a₁', a₂', d])
    | ``congrFun, #[_, _, f₁, f₂, h, a] =>
      let (got, d) ← interp h
      let (f₁', fT) ← quoteE f₁; let (f₂', _) ← quoteE f₂
      let (σ, ρ) ← splitArrow fT
      let d ← coerce d got (eqE Γ fT f₁' f₂')
      let (a', _) ← quoteE a
      match lamBody? f₁', lamBody? f₂' with
      | some b₁, some b₂ =>
        let l := instE Γ σ (tRel ρ) b₁ a'
        let r := instE Γ σ (tRel ρ) b₂ a'
        return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongrFunβ #[Γ, Δ, σ, ρ, b₁, b₂, d, a'])
      | _, _ =>
        let l := mkTApp Γ σ ρ f₁' a'
        let r := mkTApp Γ σ ρ f₂' a'
        return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongrFun #[Γ, Δ, σ, ρ, f₁', f₂', d, a'])
    | ``Eq.mpr, #[α, β, h, p] =>
      let (gh, dh) ← interp h
      let (gp, dp) ← interp p
      let α' ← quoteF α; let β' ← quoteF β
      let dh ← coerce dh gh (eqE Γ tyT α' β')
      let dp ← coerce dp gp β'
      return (α', ← rule ``Classicism.Meta.Derivable.eqMpr #[Γ, Δ, α', β', dh, dp])
    | ``Eq.mp, #[α, β, h, p] =>
      let (gh, dh) ← interp h
      let (gp, dp) ← interp p
      let α' ← quoteF α; let β' ← quoteF β
      let dh ← coerce dh gh (eqE Γ tyT α' β')
      let dp ← coerce dp gp α'
      return (β', ← rule ``Classicism.Meta.Derivable.eqMp #[Γ, Δ, α', β', dh, dp])
    | ``Eq.subst, _ =>
      -- `Eq.subst {α} {motive} {a b} h m`: the recursor with its arguments reordered
      if args.size < 6 then throwError "derive: a partially applied `Eq.subst`"
      return ← interpApp (mkConst ``Eq.ndrec ls)
        (#[args[0]!, args[2]!, args[1]!, args[5]!, args[3]!, args[4]!] ++ args.extract 6 args.size)
    | ``Eq.rec, _ | ``Eq.ndrec, _ =>
      if args.size < 6 then throwError "derive: a partially applied recursor"
      let a := args[1]!; let motive := args[2]!
      let m := args[3]!; let b := args[4]!; let h := args[5]!
      let arity : Nat := if c == ``Eq.rec then 2 else 1
      let P ← forallBoundedTelescope (← inferType motive) (some arity) fun xs _ => do
        let body := (motive.beta xs).headBeta
        if arity == 2 then
          if body.containsFVar xs[1]!.fvarId! then
            throwError "derive: a motive depends on the identity proof"
        mkLambdaFVars #[xs[0]!] body
      let (gh, dh) ← interp h
      let (gm, dm) ← interp m
      let (a', σ) ← quoteE a; let (b', _) ← quoteE b
      let (P', _) ← quoteE P
      let dh ← coerce dh gh (eqE Γ σ a' b')
      let some Pb := lamBody? P'
        | throwError "derive: a motive that is not an abstraction"
      let dm ← coerce dm gm (instE Γ σ tyT Pb a')
      let F := instE Γ σ tyT Pb b'
      let d ← rule ``Classicism.Meta.Derivable.llβ #[Γ, Δ, σ, a', b', Pb, dh, dm]
      return ← feed (mkAppN f (args.extract 0 6)) F d (args.extract 6 args.size)
    | ``And.intro, #[a, b, ha, hb] =>
      let (ga, da) ← interp ha; let (gb, db) ← interp hb
      let a' ← quoteF a; let b' ← quoteF b
      let da ← coerce da ga a'; let db ← coerce db gb b'
      return (conjE Γ a' b', ← rule ``Classicism.Meta.Derivable.andI #[Γ, Δ, a', b', da, db])
    | ``And.left, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (conjE Γ a' b')
      return (a', ← rule ``Classicism.Meta.Derivable.andE₁ #[Γ, Δ, a', b', d])
    | ``And.right, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (conjE Γ a' b')
      return (b', ← rule ``Classicism.Meta.Derivable.andE₂ #[Γ, Δ, a', b', d])
    | ``Or.inl, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g a'
      return (disjE Γ a' b', ← rule ``Classicism.Meta.Derivable.orI₁ #[Γ, Δ, a', b', d])
    | ``Or.inr, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g b'
      return (disjE Γ a' b', ← rule ``Classicism.Meta.Derivable.orI₂ #[Γ, Δ, a', b', d])
    | ``Or.elim, #[a, b, c', h, fn, g] =>
      let (gh, dh) ← interp h
      let a' ← quoteF a; let b' ← quoteF b; let c'' ← quoteF c'
      let dh ← coerce dh gh (disjE Γ a' b')
      let df ← branch fn a a' c''
      let dg ← branch g b b' c''
      return (c'', ← rule ``Classicism.Meta.Derivable.orE #[Γ, Δ, a', b', c'', dh, df, dg])
    | ``absurd, #[a, b, h, nh] =>
      let (gh, dh) ← interp h; let (gn, dn) ← interp nh
      let a' ← quoteF a; let b' ← quoteF b
      let dh ← coerce dh gh a'
      let dn ← coerce dn gn (negE Γ a')
      return (b', ← rule ``Classicism.Meta.Derivable.notE #[Γ, Δ, a', b', dh, dn])
    | ``False.elim, #[C, h] =>
      let (g, d) ← interp h
      let C' ← quoteF C
      let d ← coerce d g (botE Γ)
      return (C', ← rule ``Classicism.Meta.Derivable.botE #[Γ, Δ, C', d])
    | ``Iff.intro, #[a, b, fn, g] =>
      let a' ← quoteF a; let b' ← quoteF b
      let df ← branch fn a a' b'
      let dg ← branch g b b' a'
      return (iffE Γ a' b', ← rule ``Classicism.Meta.Derivable.iffI #[Γ, Δ, a', b', df, dg])
    | ``Iff.mp, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (iffE Γ a' b')
      return (impE Γ a' b', ← rule ``Classicism.Meta.Derivable.andE₁ #[Γ, Δ, impE Γ a' b', impE Γ b' a', d])
    | ``Iff.mpr, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (iffE Γ a' b')
      return (impE Γ b' a', ← rule ``Classicism.Meta.Derivable.andE₂ #[Γ, Δ, impE Γ a' b', impE Γ b' a', d])
    | ``Exists.intro, #[α, p, w, h] =>
      let (g, d) ← interp h
      let (p', _) ← quoteE p; let (w', σ) ← quoteE w
      let _ := α
      let ex := mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ]
      let F := mkTApp Γ (tRel (tArr σ rtE)) rtE ex p'
      if let some pb := lamBody? p' then
        let d ← coerce d g (instE Γ σ tyT pb w')
        return (F, ← rule ``Classicism.Meta.Derivable.exIβ #[Γ, Δ, σ, pb, w', d])
      let d ← coerce d g (mkTApp Γ σ rtE p' w')
      return (F, ← rule ``Classicism.Meta.Derivable.exI #[Γ, Δ, σ, p', w', d])
    | ``Exists.elim, #[α, p, b, h, fn] =>
      let (gh, dh) ← interp h
      let (p', _) ← quoteE p
      let σ ← (quoteTy α).run (← read).q
      let ex := mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ]
      let exF := mkTApp Γ (tRel (tArr σ rtE)) rtE ex p'
      let dh ← coerce dh gh exF
      let b' ← quoteF b
      let .lam wn wt wb _ := fn | throwError "derive: `Exists.elim` with a branch that is not a lambda"
      let d' ← withObj wn wt fun w => do
        let inner := wb.instantiate1 w
        let .lam hn ht hb _ := inner | throwError "derive: `Exists.elim` with a branch that is not a lambda"
        let Γ' ← ctxE
        -- the hypothesis is `p w`, as the rule states it: `F.weaken` applied to the variable
        let pw := weakenE Γ σ (tRel (tArr σ rtE)) p'
        let v0 := mkTVar Γ' σ (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, σ])
        let hf := mkTApp Γ' σ rtE pw v0
        withHyp hn ht hf fun hh => do
          let (g, d) ← interp (hb.instantiate1 hh)
          coerce d g (weakenE Γ σ tyT b')
      return (b', ← rule ``Classicism.Meta.Derivable.exE #[Γ, Δ, σ, p', b', dh, d'])
    | ``Classicism.e_exists, #[] =>
      let a := mkApp (mkConst ``Classicism.Meta.existence_e) sigE
      let pf ← logicalMember a
      let d ← rule ``Classicism.Meta.Derivable.ax #[Γ, Δ, a, pf]
      let F ← quoteF (← inferType t)
      return (F, ← coerce d (closeE Γ tyT a) F)
    | ``Classicism.em, #[p] =>
      let p' ← quoteF p
      return (disjE Γ p' (negE Γ p'), ← rule ``Classicism.Meta.Derivable.em #[Γ, Δ, p'])
    | ``True.intro, #[] | ``trivial, #[] =>
      return (mkAbbr ``Classicism.Meta.Term.top Γ #[], ← rule ``Classicism.Meta.Derivable.top #[Γ, Δ])
    | ``propext, #[a, b, h] =>
      -- Subst at the hole `a = ⬚`: the premises are the two directions of `h`, each on
      -- its own, at the logical part of the axiom set
      let a' ← quoteF a; let b' ← quoteF b
      let (d₁, d₂) ← withLogical <| withCaches do
        let (got, dh) ← interp h
        let dh ← coerce dh got (iffE Γ a' b')
        let Δ₀ ← hypsE
        let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
        let Δa := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, a', Δ₀]
        let Δb := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, b', Δ₀]
        let iff := iffE Γ a' b'
        let d₁ ← rule ``Classicism.Meta.Derivable.iffE₁ #[Γ, Δa, a', b',
          ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ₀, iff, a', dh],
          ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ₀, a']]
        let d₂ ← rule ``Classicism.Meta.Derivable.iffE₂ #[Γ, Δb, a', b',
          ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ₀, iff, b', dh],
          ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ₀, b']]
        pure (d₁, d₂)
      let eqA := mkTApp Γ tyT (tArr tyT rtE) (mkAppN (mkConst ``Classicism.Meta.Term.eq) #[sigE, Γ, tyT]) a'
      let K := mkAppN (mkConst ``Classicism.Meta.Hole.appR) #[sigE, Γ, Γ, tyT, rtE, tyT, eqA,
        mkAppN (mkConst ``Classicism.Meta.Hole.hole) #[sigE, Γ, tyT]]
      let hK ← rule ``Classicism.Meta.Derivable.refl #[Γ, Δ, tyT, a']
      let d ← rule ``Classicism.Meta.Derivable.subst #[Γ, Γ, Δ, a', b', K, d₁, d₂, hK]
      return (eqE Γ tyT a' b', d)
    | ``funext, #[_, _, f, g, h] =>
      -- ξ: the identity at a fresh variable, closed, then `substEq` at the hole
      -- `f = λv. ⬚`, and η at both ends
      let (f', fT) ← quoteE f; let (g', _) ← quoteE g
      let (σ, ρ) ← splitArrow fT
      let .lam nm d b _ := h
        | throwError "derive: `funext` whose argument is not an abstraction over the variable"
      let hd ← withLogical <| withObj nm d fun x => do
        let (got, dd) ← interp (b.instantiate1 x)
        let Γ' ← ctxE
        let v0 := mkTVar Γ' σ (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, σ])
        let exp := eqE Γ' (tRel ρ) (mkTApp Γ' σ ρ (weakenE Γ σ fT f') v0)
          (mkTApp Γ' σ ρ (weakenE Γ σ fT g') v0)
        coerce dd got exp
      let Γ' := mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, Γ]
      let v0 := mkTVar Γ' σ (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, σ])
      let eqF := mkTApp Γ fT (tArr fT rtE) (mkAppN (mkConst ``Classicism.Meta.Term.eq) #[sigE, Γ, fT]) f'
      let K := mkAppN (mkConst ``Classicism.Meta.Hole.appR) #[sigE, Γ, Γ', fT, rtE, tRel ρ, eqF,
        mkAppN (mkConst ``Classicism.Meta.Hole.lam) #[sigE, Γ, Γ', σ, ρ, tRel ρ,
          mkAppN (mkConst ``Classicism.Meta.Hole.hole) #[sigE, Γ', tRel ρ]]]
      let etaF := mkTLam Γ σ ρ (mkTApp Γ' σ ρ (weakenE Γ σ fT f') v0)
      let etaG := mkTLam Γ σ ρ (mkTApp Γ' σ ρ (weakenE Γ σ fT g') v0)
      let conv₁ := mkAppN (mkConst ``Classicism.Meta.Conv.app_congr)
        #[sigE, Γ, fT, rtE, eqF, eqF, f', etaF, convRefl Γ (tRel (tArr fT rtE)) eqF,
          convSymm Γ fT etaF f' (mkAppN (mkConst ``Classicism.Meta.Conv.eta) #[sigE, Γ, σ, ρ, f'])]
      let hK ← rule ``Classicism.Meta.Derivable.conv #[Γ, Δ, eqE Γ fT f' f', eqE Γ fT f' etaF,
        ← rule ``Classicism.Meta.Derivable.refl #[Γ, Δ, fT, f'], conv₁]
      let d ← rule ``Classicism.Meta.Derivable.substEq #[ρ, Γ, Γ', Δ, K,
        mkTApp Γ' σ ρ (weakenE Γ σ fT f') v0, mkTApp Γ' σ ρ (weakenE Γ σ fT g') v0, hd, hK]
      let conv₂ := mkAppN (mkConst ``Classicism.Meta.Conv.app_congr)
        #[sigE, Γ, fT, rtE, eqF, eqF, etaG, g', convRefl Γ (tRel (tArr fT rtE)) eqF,
          mkAppN (mkConst ``Classicism.Meta.Conv.eta) #[sigE, Γ, σ, ρ, g']]
      let d ← rule ``Classicism.Meta.Derivable.conv #[Γ, Δ, eqE Γ fT f' etaG, eqE Γ fT f' g', d, conv₂]
      return (eqE Γ fT f' g', d)
    | ``Or.casesOn, _ =>
      if args.size < 6 then throwError "derive: a partially applied `Or.casesOn`"
      let C' := (args[2]!.beta #[args[3]!]).headBeta
      return ← interpApp (mkConst ``Or.elim) (#[args[0]!, args[1]!, C', args[3]!, args[4]!, args[5]!] ++ args.extract 6 args.size)
    | ``Exists.casesOn, _ =>
      if args.size < 5 then throwError "derive: a partially applied `Exists.casesOn`"
      let C' := (args[2]!.beta #[args[3]!]).headBeta
      return ← interpApp (mkConst ``Exists.elim ls) (#[args[0]!, args[1]!, C', args[3]!, args[4]!] ++ args.extract 5 args.size)
    | ``And.casesOn, _ =>
      if args.size < 5 then throwError "derive: a partially applied `And.casesOn`"
      let a := args[0]!; let b := args[1]!; let t' := args[3]!; let k := args[4]!
      return ← interp (mkAppN k (#[mkApp3 (mkConst ``And.left) a b t', mkApp3 (mkConst ``And.right) a b t'] ++ args.extract 5 args.size)).headBeta
    | ``Iff.casesOn, _ =>
      if args.size < 5 then throwError "derive: a partially applied `Iff.casesOn`"
      let a := args[0]!; let b := args[1]!; let t' := args[3]!; let k := args[4]!
      return ← interp (mkAppN k (#[mkApp3 (mkConst ``Iff.mp) a b t', mkApp3 (mkConst ``Iff.mpr) a b t'] ++ args.extract 5 args.size)).headBeta
    | ``False.casesOn, _ =>
      if args.size < 2 then throwError "derive: a partially applied `False.casesOn`"
      let C' := (args[0]!.beta #[args[1]!]).headBeta
      return ← interpApp (mkConst ``False.elim ls) (#[C', args[1]!] ++ args.extract 2 args.size)
    | ``Iff.refl, #[a] | ``Iff.rfl, #[a] =>
      let a' ← quoteF a
      let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
      let Δa := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, a', Δ]
      let h0 ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ, a']
      let _ := Δa
      return (iffE Γ a' a', ← rule ``Classicism.Meta.Derivable.iffI #[Γ, Δ, a', a', h0, h0])
    | ``Iff.symm, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let iff := iffE Γ a' b'
      let d ← coerce d g iff
      let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
      let Δa := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, a', Δ]
      let Δb := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, b', Δ]
      let d₁ ← rule ``Classicism.Meta.Derivable.iffE₂ #[Γ, Δb, a', b',
        ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, iff, b', d],
        ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ, b']]
      let d₂ ← rule ``Classicism.Meta.Derivable.iffE₁ #[Γ, Δa, a', b',
        ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, iff, a', d],
        ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ, a']]
      return (iffE Γ b' a', ← rule ``Classicism.Meta.Derivable.iffI #[Γ, Δ, b', a', d₁, d₂])
    | ``Iff.trans, #[a, b, c', h₁, h₂] =>
      let (g₁, d₁) ← interp h₁; let (g₂, d₂) ← interp h₂
      let a' ← quoteF a; let b' ← quoteF b; let c'' ← quoteF c'
      let d₁ ← coerce d₁ g₁ (iffE Γ a' b'); let d₂ ← coerce d₂ g₂ (iffE Γ b' c'')
      let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
      let Δa := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, a', Δ]
      let Δc := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, c'', Δ]
      let w₁a ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, iffE Γ a' b', a', d₁]
      let w₂a ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, iffE Γ b' c'', a', d₂]
      let w₁c ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, iffE Γ a' b', c'', d₁]
      let w₂c ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, iffE Γ b' c'', c'', d₂]
      let e₁ ← rule ``Classicism.Meta.Derivable.iffE₁ #[Γ, Δa, b', c'', w₂a,
        ← rule ``Classicism.Meta.Derivable.iffE₁ #[Γ, Δa, a', b', w₁a, ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ, a']]]
      let e₂ ← rule ``Classicism.Meta.Derivable.iffE₂ #[Γ, Δc, a', b', w₁c,
        ← rule ``Classicism.Meta.Derivable.iffE₂ #[Γ, Δc, b', c'', w₂c, ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ, c'']]]
      return (iffE Γ a' c'', ← rule ``Classicism.Meta.Derivable.iffI #[Γ, Δ, a', c'', e₁, e₂])
    | _, _ =>
      if (`Classicism).isPrefixOf c then
        if let some (.thmInfo _) := (← getEnv).find? c then
          let mut k := 0
          for a in args do
            if ← isParam a then k := k + 1 else break
          let params := args.extract 0 k
          let thm ← ensureSpecialized c ls params
          let (S, d) ← citeTheorem (mkAppN f params) thm
          return ← feed (mkAppN f params) S d (args.extract k args.size)
      if coreUnfolded.contains c || (← isMatcher c) then
        let info ← getConstInfo c
        return ← interp (((info.value! (allowOpaque := true)).instantiateLevelParams info.levelParams ls).beta args).headBeta
      if let some t' ← unfoldDefinition? t then return ← interp t'
      let t' ← whnfCore t
      if t' != t then return ← interp t'
      let t'' ← whnfR t
      if t'' != t then return ← interp t''
      throwError "derive: no rule for the constant {c}"
  let (F, d) ← interp f
  feed f F d args

/-- The sentence for a closed statement, in the empty context. -/
partial def closedQuote (stmt : Expr) : TrM Expr := do
  withReader (fun c => { c with q := { c.q with objVars := [] }, hyps := [] }) (withCaches (quoteF stmt))

/-- Apply a derived function to its remaining arguments: modus ponens for a proof, `UI`
for a term. -/
partial def feed (cur : Expr) (F d : Expr) (args : Array Expr) : TrM (Expr × Expr) := do
  let mut cur := cur
  let mut F := F
  let mut d := d
  for a in args do
    let Γ ← ctxE
    let Δ ← hypsE
    let .forallE nm dom body _ ← whnf (← inferType cur)
      | throwError "derive: {cur} is applied to {a} but is not a function"
    -- a codomain mentioning the bound variable only through a motive's redex does not depend on it
    let body := betaDeep body
    if ← isProp dom then
      if body.hasLooseBVars then throwError "derive: a formula depends on a proof: {cur}"
      let (ga, da) ← interp a
      let A ← quoteF dom
      let da ← coerce da ga A
      if (← whnfR body).isConstOf ``False then
        d ← coerce d F (negE Γ A)
        d ← rule ``Classicism.Meta.Derivable.notE #[Γ, Δ, A, botE Γ, da, d]
        F := botE Γ
      else
        let B ← quoteF body
        d ← coerce d F (impE Γ A B)
        d ← rule ``Classicism.Meta.Derivable.impE #[Γ, Δ, A, B, d, da]
        F := B
    else
      if ← isParam' dom then throwError "derive: a type argument after the leading parameters"
      let σ ← (quoteTy dom).run (← read).q
      let (bodyF, _) ← quoteE (.lam nm dom body .default)
      let some B := lamBody? bodyF
        | throwError "derive: internal error, a quantifier body that is not an abstraction"
      let allF := mkAbbr ``Classicism.Meta.Term.forall' Γ #[σ, B]
      d ← coerce d F allF
      let (a', _) ← quoteE a
      d ← rule ``Classicism.Meta.Derivable.allEβ #[Γ, Δ, σ, B, d, a']
      F := instE Γ σ tyT B a'
    cur := mkApp cur a
  return (F, d)

/-- Cite a closed theorem `thm : Theorem Ax S₀` for the proof term `t`: the sentence is
placed in the context and converted to the quotation of `t`'s type. -/
partial def citeTheorem (t thm : Expr) : TrM (Expr × Expr) := do
  let Γ ← ctxE
  let Δ ← hypsE
  let S ← quoteF (← inferType t)
  let thmTy ← instantiateMVars (← inferType thm)
  let some S₀ := thmTy.getAppArgs[2]?
    | throwError "derive: internal error, a citation of{indentExpr thm}\nwhich is not a theorem"
  let thm ← liftLogical thm
  let d ← rule ``Classicism.Meta.Derivable.ofTheorem #[Γ, Δ, S₀, thm]
  -- a theorem cited at a constructor type has its operations there unfolded, by δ in
  -- the empty context, carried into this one by renaming
  let nil : Expr := mkApp (mkConst ``List.nil [Level.zero]) tyE
  let (S₀', p) ← unfoldConv nil S₀
  let (cur, d) ← match p with
    | none => pure (closeE Γ tyT S₀, d)
    | some p =>
      let r := mkApp (mkConst ``Classicism.Meta.Ren.ofEmpty) Γ
      let c := mkAppN (mkConst ``Classicism.Meta.Conv.rename) #[sigE, nil, Γ, tyT, r, S₀, S₀', p]
      let cur := closeE Γ tyT S₀'
      pure (cur, ← rule ``Classicism.Meta.Derivable.conv #[Γ, Δ, closeE Γ tyT S₀, cur, d, c])
  let d ← coerce d cur S
  return (S, d)

/-- The leading parameters of a theorem's type: for each, its kind as an object type
variable, `none` for an instance. A type is `.ty`; one carrying an instance of a class
other than `Ty` is relational, `.rty`. -/
partial def paramKinds (ty : Expr) : MetaM (Array (Option Kind)) :=
  forallTelescope ty fun xs _ => do
    let mut kinds : Array (Option Kind) := #[]
    for x in xs do
      let t ← whnf (← inferType x)
      if t.isSort && !t.isProp then kinds := kinds.push (some .ty)
      else if let some cls := (← isClass? t) then
        if cls != ``Classicism.Ty then
          let σ := t.getAppArgs[0]!
          if let some idx := xs.findIdx? (· == σ) then
            if idx < kinds.size then kinds := kinds.set! idx (some .rty)
        kinds := kinds.push none
      else break
    return kinds

/-- Translate the theorem `c` once, at metalogical type parameters for its shallow ones,
and declare the result as `name : ∀ σ' … ρ' …, Theorem Ax (S σ' … ρ' …)`. A class
instance among its parameters becomes nothing: the class's operations at the variable
are the object constants, and its laws are derived by induction on the type. -/
partial def translateGeneric (c : Name) (ls : List Level) (name : Name) : TrM Unit := do
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
          let d ← coerce d got S
          let thmTy := mkAppN (mkConst ``Classicism.Meta.Theorem) #[sigE, ax, S]
          return (← mkForallFVars tvs thmTy, ← mkLambdaFVars tvs d)
    go 0 [] #[]
  modify fun s => { s with specs := s.specs.erase keyS }
  let t₀ ← IO.monoMsNow
  timed "addDecl" (withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := dty, value := dval }))
  trace s!"  ✓ {c}: kernel {(← IO.monoMsNow) - t₀} ms, depth {dval.approxDepth}"
  modify fun s => { s with timing := s.timing.insert "translations" (s.timing.getD "translations" 0 + 1) }
  restoreMemo saved

/-- The library theorem `c` cited at the parameters `params`, as a `Theorem`: its
generic translation `c.derivable`, made on first use, applied to the object types the
citation's type parameters quote to. Inside an induction on the object type, a lemma
whose parameters involve the instance under induction is instead specialized at those
very parameters, taking the induction hypothesis as a further parameter, since its
general translation would need the law being derived. -/
partial def ensureSpecialized (c : Name) (ls : List Level) (params : Array Expr) : TrM Expr := do
  -- a law of a mirror class, cited as its projection function: the induction hypothesis
  -- if it is the law being derived at the instance under induction, else the law derived
  -- for every object type, at this one
  if let some pinfo ← getProjectionFnInfo? c then
    let cls := pinfo.ctorName.getPrefix
    if (inductionInstances cls).isSome then
      let some inst := params[pinfo.numParams]?
        | throwError "derive: the law {c} cited without its instance"
      if let Expr.fvar fid := inst then
        if let some (_, _, ih) := (← read).ihs.find? (fun (f, j, _) => f == fid && j == pinfo.i) then
          return ih
      let name ← ensureFieldInduction cls pinfo.i
      return mkApp (mkConst name) (← (quoteRTy params[0]!).run (← read).q)
  let ihArgs := ((← read).ihs.filter fun (fid, _, _) => params.any (·.containsFVar fid)).toArray.map (·.2.2)
  unless ihArgs.isEmpty do return ← specializeUnderIH c ls params ihArgs
  let name := c ++ (if (← read).axIsC then `derivableC else `derivable)
  unless (← getEnv).contains name do translateGeneric c ls name
  let kinds ← paramKinds (← getConstInfo c).type
  unless kinds.size ≤ params.size do
    throwError "derive: {c} cited with too few parameters"
  let qc := (← read).q
  let mut tys : Array Expr := #[]
  for i in [0:kinds.size] do
    match kinds[i]! with
    | some .ty => tys := tys.push (← (quoteTy params[i]!).run qc)
    | some .rty => tys := tys.push (← (quoteRTy params[i]!).run qc)
    | none => pure ()
  return mkAppN (mkConst name) tys

/-- The specialization of `c` at parameters that involve an instance under induction,
declared as `c.derivable_n`, abstracted over the metalogical type parameters in scope and the
induction hypotheses the parameters involve, and applied to them. -/
partial def specializeUnderIH (c : Name) (ls : List Level) (params : Array Expr) (ihArgs : Array Expr) : TrM Expr := do
  let tyFvars := (← read).q.tyVars.reverse.toArray.map (fun (id, _, _) => mkFVar id)
  let tvs := (← read).q.tyVars.reverse.toArray.map (·.2.2)
  let key ← mkLambdaFVars tyFvars (mkAppN (mkConst c ls) params)
  let keyS := s!"{(← read).axIsC}|{key}"
  let name := c ++ Name.mkSimple s!"derivable_{hash keyS}"
  if (← getEnv).contains name then return mkAppN (mkConst name) (tvs ++ ihArgs)
  let saved ← get
  if (← get).specs.contains keyS then
    throwError "derive: {c} depends on itself at these types"
  let info ← getConstInfo c
  let .thmInfo _ := info | throwError "derive: {c} is not a theorem"
  trace s!"  specializing {c} ({(← get).specs.size} in progress, under an induction hypothesis)"
  let body := (((info.value! (allowOpaque := true)).instantiateLevelParams info.levelParams ls).beta params).headBeta
  let stmt ← instantiateForall info.type params
  modify fun s => { s with specs := s.specs.insert keyS }
  let (ty, val) ← withReader (fun c => { c with q := { c.q with objVars := [] }, hyps := [], logicalDepth := 0 }) <| withCaches do
    let S ← quoteF stmt
    let (got, d) ← interp body
    let d ← coerce d got S
    let thmTy := mkAppN (mkConst ``Classicism.Meta.Theorem) #[sigE, (← read).ax, S]
    return (← mkForallFVars (tvs ++ ihArgs) thmTy, ← mkLambdaFVars (tvs ++ ihArgs) d)
  modify fun s => { s with specs := s.specs.erase keyS }
  let t₀ ← IO.monoMsNow
  timed "addDecl" (withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := ty, value := val }))
  trace s!"  ✓ {c} (under a hypothesis): kernel {(← IO.monoMsNow) - t₀} ms"
  modify fun s => { s with timing := s.timing.insert "specializations" (s.timing.getD "specializations" 0 + 1) }
  restoreMemo saved
  return mkAppN (mkConst name) (tvs ++ ihArgs)

/-- The law `i` of the mirror class `cls`, derived for every object type by induction on
the type and declared as `cls.law.derivable : ∀ τ', Theorem Ax (S τ')`. The base case is
the translation of the `Prop` instance's proof of the law; the step is the translation
of the arrow instance's, with the law at the smaller type, cited through the instance
variable, as the induction hypothesis. The recursion is `RTy.rec`. -/
partial def ensureFieldInduction (cls : Name) (i : Nat) : TrM Name := do
  let some (instP, instA) := inductionInstances cls
    | throwError "derive: no instances registered for induction on {cls}"
  let some sinfo := getStructureInfo? (← getEnv) cls
    | throwError "derive: {cls} is not a structure"
  let some field := sinfo.fieldNames[i]?
    | throwError "derive: {cls} has no field {i}"
  let ax := (← read).ax
  let name := cls ++ field ++ (if (← read).axIsC then `derivableC else `derivable)
  if (← getEnv).contains name then return name
  let keyS := name.toString
  if (← get).specs.contains keyS then
    throwError "derive: the law {cls ++ field} depends on itself at the same type"
  let saved ← get
  modify fun s => { s with specs := s.specs.insert keyS }
  trace s!"  deriving {cls ++ field} by induction on the type"
  let rtyE : Expr := Lean.mkConst ``Classicism.Meta.RTy
  let fresh (q : QCtx) (ihs : List (FVarId × Nat × Expr)) : TCtx → TCtx :=
    fun c => { c with q := q, hyps := [], ihs := ihs, logicalDepth := 0 }
  -- the law as a sentence, a function of the object type
  let projTy := (← getConstInfo (cls ++ field)).type
  let some pinfo ← getProjectionFnInfo? (cls ++ field)
    | throwError "derive: {cls ++ field} is not a projection"
  let (motive, S) ← withLocalDeclD `τ' rtyE fun tv => do
    -- only the class's parameters and the instance: the law's own binders stay in the
    -- statement, as the quantifiers they are
    forallBoundedTelescope projTy (some (pinfo.numParams + 1)) fun xs stmt => do
      let τ := xs[0]!
      let q : QCtx := { tyVars := [(τ.fvarId!, .rty, tv)] }
      let S ← withReader (fresh q []) (withCaches (quoteF stmt))
      let thmTy := mkAppN (mkConst ``Classicism.Meta.Theorem) #[sigE, ax, S]
      return (← mkLambdaFVars #[tv] thmTy, ← mkLambdaFVars #[tv] S)
  -- the base case, at `t`: the `Prop` instance's proof
  let nil : Expr := mkApp (mkConst ``List.nil [Level.zero]) tyE
  let hypsNil : Expr := mkApp (mkConst ``List.nil [Level.zero])
    (mkApp2 (mkConst ``Classicism.Meta.Formula) sigE nil)
  -- coerce to the law at a constructor type: its operations unfolded first, by δ
  let toLaw (got d law : Expr) : TrM Expr := do
    let (law', p) ← unfoldConv nil law
    let d ← coerce d got law'
    match p with
    | none => pure d
    | some p =>
      let p' := mkAppN (mkConst ``Classicism.Meta.Conv.symm) #[sigE, nil, tyT, law, law', p]
      rule ``Classicism.Meta.Derivable.conv #[nil, hypsNil, law', law, d, p']
  let base ← withReader (fresh {} []) <| withCaches do
    let (got, d) ← interp (Expr.proj cls i (mkConst instP))
    toLaw got d (S.beta #[mkConst ``Classicism.Meta.RTy.t])
  -- the step, at `σ' ⇒ ρ'`: the arrow instance's proof, with the law at `ρ'` given
  let step ← withLocalDeclD `σ' tyE fun sv => withLocalDeclD `ρ' rtyE fun rv => do
    withLocalDeclD `ih (motive.beta #[rv]) fun ih => do
      forallTelescope (← getConstInfo instA).type fun xs _ => do
        -- the instance's binders: two types, then instances; the one of `cls` at the
        -- second type carries the hypothesis
        let mut tyVars : List (FVarId × Kind × Expr) := []
        let mut ihs : List (FVarId × Nat × Expr) := []
        let mut k := 0
        for x in xs do
          let xt ← whnf (← inferType x)
          if xt.isSort then
            if k == 0 then tyVars := (x.fvarId!, .ty, sv) :: tyVars
            else if k == 1 then tyVars := (x.fvarId!, .rty, rv) :: tyVars
            else throwError "derive: the instance {instA} has more than two type parameters"
            k := k + 1
          else if xt.isAppOf cls && xt.getAppArgs[0]! == xs[1]! then
            ihs := (x.fvarId!, i, ih) :: ihs
        let d ← withReader (fresh { tyVars := tyVars } ihs) <| withCaches do
          let (got, d) ← interp (Expr.proj cls i (mkAppN (mkConst instA) xs))
          toLaw got d (S.beta #[tArr sv rv])
        mkLambdaFVars #[sv, rv, ih] d
  modify fun s => { s with specs := s.specs.erase keyS }
  -- the declaration
  let (ty, val) ← withLocalDeclD `τ' rtyE fun tv => do
    let motive₁ := mkLambda `_ .default tyE (mkConst ``True)
    let eCase : Expr := Lean.mkConst ``True.intro
    let relCase ← withLocalDeclD `a rtyE fun a => withLocalDeclD `h (motive.beta #[a]) fun h =>
      mkLambdaFVars #[a, h] (mkConst ``True.intro)
    let varCase ← withLocalDeclD `i (mkConst ``Nat) fun i =>
      mkLambdaFVars #[i] (mkConst ``True.intro)
    let arrCase ← withLocalDeclD `a tyE fun a => withLocalDeclD `b rtyE fun b =>
      withLocalDeclD `h (mkConst ``True) fun h => withLocalDeclD `ih (motive.beta #[b]) fun ih =>
        mkLambdaFVars #[a, b, h, ih] (mkAppN step #[a, b, ih])
    let recE := mkAppN (mkConst ``Classicism.Meta.RTy.rec [Level.zero])
      #[motive₁, motive, eCase, relCase, varCase, base, arrCase, tv]
    return (← mkForallFVars #[tv] (motive.beta #[tv]), ← mkLambdaFVars #[tv] recE)
  let t₀ ← IO.monoMsNow
  timed "addDecl" (withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := ty, value := val }))
  trace s!"  ✓ {cls ++ field} by induction: kernel {(← IO.monoMsNow) - t₀} ms"
  modify fun s => { s with timing := s.timing.insert "inductions" (s.timing.getD "inductions" 0 + 1) }
  restoreMemo saved
  return name

end

/-! ### The command -/

/-- Derive `foo`: declare `foo.derivable`, its generic translation, in `C` if its proof
uses Existence and in `C⁻` otherwise. -/
def derive (foo : Name) : TermElabM Unit := do
  let info ← getConstInfo foo
  let .thmInfo _ := info | throwError "derive: {foo} is not a theorem"
  let axs ← collectAxioms foo
  let axIsC := axs.contains ``Classicism.e_exists
  let ax := mkApp (mkConst (if axIsC then ``Classicism.Meta.C.axioms else ``Classicism.Meta.C.axiomsMinus)) sigE
  let tctx : TCtx := { ax := ax, axIsC := axIsC }
  let ((), st) ← (translateGeneric foo [] (foo ++ `derivable)).run tctx |>.run {}
  if Classicism.Meta.Translate.profile.get (← getOptions) then
    logInfo m!"profile (ms): {st.timing.toList}"

syntax (name := classicismDerive) "#classicism_derive " ident+ : command

@[command_elab classicismDerive] def elabDerive : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      let env ← getEnv
      unless env.contains (n ++ `derivable) || env.contains (n ++ `derivableC) do
        withScope (fun sc => { sc with opts := maxHeartbeats.set sc.opts 0 }) (liftTermElabM (derive n))
      let dn := if (← getEnv).contains (n ++ `derivable) then n ++ `derivable else n ++ `derivableC
      let ty := (← getConstInfo dn).type
      let inC := ty.find? (·.isConstOf ``Classicism.Meta.C.axioms) |>.isSome
      logInfo m!"{n} ⟶ {dn} : {ty}\nderived ✓ in {if inC then "C" else "C⁻"}"
    catch ex =>
      logError m!"{n}: not derived — {ex.toMessageData}"

/-- `#classicism_derive_audit Mod …` derives every theorem of the modules, and reports. -/
syntax (name := classicismDeriveAudit) "#classicism_derive_audit " ident+ : command

@[command_elab classicismDeriveAudit] def elabDeriveAudit : CommandElab := fun stx => do
  for modId in stx[1].getArgs do
    let env ← getEnv
    let some idx := env.getModuleIdx? modId.getId
      | logError m!"no module {modId.getId}"; continue
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .thmInfo _ := ci then
          -- a class field is derived by induction on the type, on demand, not on its own
          unless n.isInternal || (← liftTermElabM (getProjectionFnInfo? n)).isSome do
            names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    let mut ok : Nat := 0
    let mut failures : Array MessageData := #[]
    let mut i := 0
    let mut times : Array String := #[]
    -- a line per theorem, with the time it took, appended to the progress file as it
    -- happens; the heartbeat limit is the file's, so that a runaway fails rather than
    -- running on
    let progressFile := Classicism.Meta.Translate.progress.get (← getOptions)
    let report (line : String) : CommandElabM Unit := do
      unless progressFile == "" do
        IO.FS.withFile progressFile .append fun h => h.putStrLn line
    for n in names do
      i := i + 1
      let t₀ ← IO.monoMsNow
      let line ← try
          let env ← getEnv
          unless env.contains (n ++ `derivable) || env.contains (n ++ `derivableC) do
            liftTermElabM (derive n)
          ok := ok + 1
          pure s!"[{i}/{names.size}] {n} ✓ {(← IO.monoMsNow) - t₀} ms"
        catch ex =>
          failures := failures.push m!"{n}: {ex.toMessageData}"
          pure s!"[{i}/{names.size}] {n} ✗ {(← IO.monoMsNow) - t₀} ms"
      times := times.push line
      report line
    logInfo m!"{modId.getId}: {ok} of {names.size} theorems derived\n\
{MessageData.joinSep failures.toList "\n"}\n{"\n".intercalate times.toList}"

end Classicism.Meta.Translate
