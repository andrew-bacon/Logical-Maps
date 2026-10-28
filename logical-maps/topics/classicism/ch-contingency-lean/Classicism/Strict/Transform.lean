import Classicism.Strict.Primitives
import Classicism.Tools.Check

/-!
# The transformer: Appendix A as an induction on Lean proof terms

`#classicism_transform foo` takes a theorem `foo : S` proved under the **gate**, where
`propext` and `funext` occur only with closed arguments, and produces, from the eleven
closed identities and no `propext` or `funext` at all,

* `foo.nec : S' = ⊤`, the **necessitation** of `foo`, and
* `foo.strict : S'`,

where `S'` is `S` read in the paper's vocabulary (`True ↦ ⊤`, `False ↦ ⊥`, `→ ↦ imp`,
`↔ ↦ iff`). The kernel checks both, so a bug here yields a rejected declaration, never a
false theorem.

No statement quantifies over types: the type-system check allows a binder over a type
only as a parameter of a declaration, so every theorem is a formula of the paper's
language once its type parameters are fixed, and every theorem has a necessitation. That
is what puts the whole shallow layer within reach of one induction.

## The method

This is Appendix A's `hardlemma`, done as the paper does it: by **induction on the given
proof**, never by re-proving anything. Nothing is decided and nothing is searched for; each
constructor of the proof term has one fixed lemma, and the transform of a proof is those
lemmas composed in the shape of the proof. So a new shallow theorem needs no new strict
work, provided its proof is built from constructors already in the table.

`H` is a Hilbert system and a Lean term is a natural deduction, so the induction hypothesis
is carried in sequent form. For a proof `t : A` in a context with object variables `v̄` and
hypotheses `h₁ : H₁, …, hₙ : Hₙ`, the transform of `t` is a proof of

    (λv̄. Γ → A') = (λv̄. ⊤)          Γ := ⊤ ∧ H₁' ∧ … ∧ Hₙ'

an identity in the algebra `v̄ → Prop` of `Classicism/Algebra.lean`. The cases:

| proof term | what carries the induction |
| --- | --- |
| a hypothesis `hᵢ` | `rule_hyp`, then `rule_weaken` past the later hypotheses |
| `fun h : H => b` | `rule_imp_intro` |
| `f a`, `a` a proof | `rule_imp_elim`, or `rule_not_elim`: Appendix A step (i) |
| `fun u : σ => b` | Distribution-∨∀, the hypothesis under `∀u`, Proposition A.1: step (ii) |
| `f a`, `a` a term | Absorption-∨∀, then `rule_absorb`: case (ii) |
| a constant `c : S` | its necessitation `S' = ⊤`, then `rule_const` |
| gated `propext s` | `s` transformed with `Γ` empty, then Proposition A.3 |
| gated `funext (fun x => s)` | `s` transformed with `x` added to `v̄`; η does the rest |

A library theorem is a constant like any other, its necessitation being its own transform,
made on demand. The core constants (`And.intro`, `Or.elim`, `Eq.refl`, …) have theirs in
`Classicism/Primitives.lean`. Recursors are first restated with their motives instantiated,
as `Prim.ll`, `Prim.and_rec` and so on, so that their types are formulas.

Every step is `congrArg` on a closed identity with β for free, which is Ref and Leibniz's
Law. There is no ξ: nothing is ever proved pointwise and then abstracted.

## Why the gate is exactly the right condition

The `propext` case transforms its argument with `Γ` *empty*, because Equivalence needs
`(λv̄. A ↔ B) = (λv̄. ⊤)` outright, not under hypotheses. That is sound only if the argument
mentions no hypothesis in scope, which is what the gate checks. The natural-deduction
presentation of `C` says the same thing: its special rule has premises `P ⊢ Q` and `Q ⊢ P`
with no side premises.
-/

open Lean Meta Elab Command

namespace Classicism.Check

/-- The name of the necessitation of `n`. -/
def necName (n : Name) : Name := n ++ `nec
/-- The name of the strict restatement of `n`. -/
def strictName (n : Name) : Name := n ++ `strict

/-- Where the hand-proved necessitation of a core constant lives. -/
def primNecName (c : Name) : Name := (`Classicism.Strict.Nec).str (c.toString (escape := false))

register_option classicism.transform.check : Bool := {
  defValue := false
  descr := "type-check every intermediate proof the transformer builds (slow; for debugging)"
}

/-! ### The registry of mirrors

A class such as `Rel` states its laws with `True` and proves them, in its instances, by
gated Equivalence. The strict layer has a **mirror** of each such class, whose laws are
closed identities proved from the axioms (`Classicism/Mirror.lean`). The transformer has to
know which constant mirrors which: the class, its data projections and its instances go in
`mirrorExt`, and each law field's necessitation goes in `necExt`. Both are filled by
commands, so a new class needs a mirror but no change here. -/

/-- Constants and their strict mirrors. -/
initialize mirrorExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (a, b) => m.insert a b
    addImportedFn := fun ass => ass.foldl (fun m as => as.foldl (fun m (a, b) => m.insert a b) m) {}
  }

/-- Constants and their necessitations, where those are not found by name. -/
initialize necExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (a, b) => m.insert a b
    addImportedFn := fun ass => ass.foldl (fun m as => as.foldl (fun m (a, b) => m.insert a b) m) {}
  }

/-- Context of the induction: the object variables `v̄` in scope, and the hypotheses in
scope with their formulas already read in the paper's vocabulary. -/
structure ICtx where
  vars : Array Expr := #[]
  hyps : Array (FVarId × Expr) := #[]
  /-- Parameters whose types read differently, such as `inst : Rel τ`, and the variables
  of the mirrored types that stand for them. -/
  subst : FVarIdMap Expr := {}

/-- State: which definitions have been given strict twins (`none`: needs none). -/
structure TrState where
  twins : NameMap (Option Name) := {}
  inProgress : NameSet := {}

abbrev TrM := ReaderT ICtx (StateRefT TrState MetaM)

/-! ### Reading a formula in the paper's vocabulary -/

mutual

/-- `True ↦ ⊤`, `False ↦ ⊥`, `Iff ↦ iff`, `A → False ↦ ¬A`, any other arrow between
propositions `↦ imp`, `a ≠ b ↦ ¬(a = b)`. A defined constant whose definition mentions any
of these is sent to a strict twin, made on demand, so that the reading commutes with
unfolding definitions. Predicate types such as `σ → Prop` are left alone. -/
partial def translate (e : Expr) : TrM Expr := do
  match e with
  | .const c ls =>
    if c == ``True then return mkConst ``Classicism.Strict.Top
    if c == ``False then return mkConst ``Classicism.Strict.Bot
    if c == ``Classicism.Box then return mkConst ``Classicism.Strict.Box
    if c == ``Classicism.Dia then return mkConst ``Classicism.Strict.Dia
    if let some c' := (mirrorExt.getState (← getEnv)).find? c then return mkConst c' ls
    match ← twin c with
    | some c' => return mkConst c' ls
    | none => return e
  | .app .. =>
    match e.getAppFnArgs with
    | (``Iff, #[a, b]) =>
      return mkApp2 (mkConst ``Classicism.iff) (← translate a) (← translate b)
    | (``Ne, #[α, a, b]) =>
      return mkNot (mkApp3 (mkConst ``Eq [Level.one]) α (← translate a) (← translate b))
    | _ =>
      let f ← translate e.getAppFn
      let args ← e.getAppArgs.mapM translate
      return mkAppN f args
  | .forallE nm d b bi =>
    if !b.hasLooseBVars then
      if ← isProp d then
        if ← isProp b then
          if b.isConstOf ``False then return mkNot (← translate d)
          return mkApp2 (mkConst ``Classicism.imp) (← translate d) (← translate b)
    let d' ← translate d
    withLocalDecl nm bi d' fun x => do
      mkForallFVars #[x] (← translate (b.instantiate1 x))
  | .lam nm d b bi =>
    let d' ← translate d
    withLocalDecl nm bi d' fun x => do
      mkLambdaFVars #[x] (← translate (b.instantiate1 x))
  | .mdata _ b => translate b
  | .fvar id => return ((← read).subst.get? id).getD e
  | _ => return e

/-- The strict twin of a library definition, if its definition reads differently in the
paper's vocabulary. -/
partial def twin (c : Name) : TrM (Option Name) := do
  if !(`Classicism).isPrefixOf c || (`Classicism.Strict).isPrefixOf c
      || (`Classicism.Axiomatic).isPrefixOf c then return none
  if let some r := (← get).twins.find? c then return r
  let env ← getEnv
  if (necExt.getState env).contains c then return none
  if env.contains (strictName c) then
    modify fun s => { s with twins := s.twins.insert c (strictName c) }
    return some (strictName c)
  let some (.defnInfo info) := env.find? c | return none
  -- provisional, so that a definition mentioning itself cannot loop
  modify fun s => { s with twins := s.twins.insert c none }
  let value' ← withReader (fun _ => {}) (translate info.value)
  let type' ← withReader (fun _ => {}) (translate info.type)
  if value' == info.value && type' == info.type then return none
  addDecl (.defnDecl { info with name := strictName c, type := type', value := value' })
  setReducibilityStatus (strictName c) (← getReducibilityStatus c)
  modify fun s => { s with twins := s.twins.insert c (strictName c) }
  return some (strictName c)

end

/-! ### The algebra of the current context -/

private def propE : Expr := mkSort Level.zero
private def topP : Expr := mkConst ``Classicism.Strict.Top

/-- `λv̄. e`. -/
def lamV (e : Expr) : TrM Expr := do mkLambdaFVars (← read).vars e

/-- The algebra `v̄ → Prop` and its `BA` instance. -/
def algebra : TrM (Expr × Expr) := do
  let T ← mkForallFVars (← read).vars propE
  let inst ← try synthInstance (mkApp (mkConst ``Classicism.Strict.BA) T) catch _ =>
    throwError "transform: no Boolean algebra on {T}; is a variable's type outside R?"
  return (T, inst)

/-- The prefixes `Γ₀ = ⊤`, `Γ₁ = Γ₀ ∧ H₁`, …, `Γₙ`, pointwise. -/
def gammas : TrM (Array Expr) := do
  let mut acc := #[topP]
  for (_, H) in (← read).hyps do
    acc := acc.push (mkAnd acc.back! H)
  return acc

/-- `Γ`, pointwise. -/
def gamma : TrM Expr := return (← gammas).back!

/-- Apply a lemma of `Classicism/Rules.lean` in the current algebra. -/
def rule (n : Name) (args : Array Expr) : TrM Expr := do
  let (T, inst) ← algebra
  let r := mkAppN (mkConst n) (#[T, inst] ++ args)
  if classicism.transform.check.get (← getOptions) then
    try Meta.check r catch ex =>
      throwError "transform: internal error applying {n}:\n{ex.toMessageData}"
  return r

/-- A closed identity `c : L = R` between `k`-ary functions, applied to `k` arguments under
`λv̄`: a proof of `(λv̄. L args) = (λv̄. R args)`. One `congrArg`, which is Ref and Leibniz's
Law; β, which is free, exposes the instance. This is every "(identity), β" step of
Appendix A. -/
def liftClosed (c : Expr) (args : Array Expr) : TrM Expr := do
  let some (K, _, _) := (← inferType c).eq? | throwError "transform: {c} is not an identity"
  let m ← withLocalDeclD `K K fun k => do
    mkLambdaFVars #[k] (← lamV (mkAppN k args))
  mkCongrArg m c

/-- The `Ty σ` evidence that `σ` is a type of `R`. -/
def tyInst (σ : Expr) : TrM Expr := do
  try synthInstance (mkApp (mkConst ``Classicism.Ty) σ) catch _ =>
    throwError "transform: {σ} is not known to be a type of R (no `Ty` instance)"

/-- Is this argument a type or type-system evidence, as opposed to an object or a proof? -/
def isParam (a : Expr) : MetaM Bool := do
  let t ← whnf (← inferType a)
  if let .sort l := t then
    -- `a` is a type, unless it is a proposition (`a : Prop`), which is an object of type `t`
    return !(l.isZero)
  return (← isClass? t).isSome

/-! ### The induction

`interp` returns the formula it has proved together with the proof. The formula is tracked
rather than recomputed from Lean's types, because Lean identifies `¬A` with `A → False`
while their readings, `¬A'` and `¬A' ∨ ⊥`, are Boolean-equivalent but not identical. Where
a proof is used at a formula other than the one it was built at, `coerce` bridges the two. -/

/-- Core theorems unfolded at their use rather than cited: the ones `simp` leaves in a
proof term. The same list as the translator's `Classicism.Meta.Translate.coreUnfolded`. -/
def coreUnfolded : List Name :=
  [``of_eq_true, ``of_eq_false, ``eq_true, ``eq_false, ``eq_self, ``congr, ``congrFun',
   ``forall_congr]

mutual

/-- The transform of a proof `t : A`: the formula `A'` it establishes, and a proof of
`(λv̄. Γ → A') = (λv̄. ⊤)`. -/
partial def interp (t : Expr) : TrM (Expr × Expr) := do
  let t := (← instantiateMVars t).consumeMData.headBeta
  match t with
  | .letE _ _ v b _ => interp (b.instantiate1 v)
  | .fvar id => interpHyp id
  | .lam nm d b bi =>
    if ← isProp d then
      -- `fun h : H => b`
      let H' ← translate d
      let G ← lamV (← gamma)
      let HL ← lamV H'
      withLocalDecl nm bi d fun h => do
        let (B', pb) ← withReader (fun c => { c with hyps := c.hyps.push (h.fvarId!, H') })
          (interp (b.instantiate1 h))
        let pf ← rule ``Classicism.Strict.BA.rule_imp_intro #[G, HL, ← lamV B', pb]
        return (mkApp2 (mkConst ``Classicism.imp) H' B', pf)
    else
      if ← isParam' d then
        throwError "transform: a proof abstracts over a type or an instance inside a \
formula; such a family of formulas has no single identity form"
      -- `fun u : σ => b`: Appendix A, inductive step (ii)
      let inst ← tyInst d
      let Γ ← gamma
      withLocalDecl nm bi d fun u => do
        let (B', pb) ← withReader (fun c => { c with vars := c.vars.push u })
          (interp (b.instantiate1 u))
        let Bfun ← mkLambdaFVars #[u] B'
        -- (λv̄. ¬Γ ∨ ∀u.B) = (λv̄. ∀u. ¬Γ ∨ B)            Distribution-∨∀, β
        let ax := mkApp2 (mkConst ``Classicism.Axiomatic.distribution_or_forall) d inst
        let step₁ ← liftClosed ax #[Bfun, mkNot Γ]
        --                   = (λv̄. ∀u. ⊤)                 the induction hypothesis, under ∀u
        let step₂ ← mkCongrArg (← underForall u) pb
        --                   = (λv̄. ⊤)                     Proposition A.1
        let m₃ ← withLocalDeclD `r propE fun r => do mkLambdaFVars #[r] (← lamV r)
        let step₃ ← mkCongrArg m₃ (mkApp2 (mkConst ``Classicism.Strict.forall_const_top) d inst)
        return (← mkForallFVars #[u] B', ← mkEqTrans step₁ (← mkEqTrans step₂ step₃))
  | .proj S i e =>
    let ty ← whnf (← inferType e)
    match S, i, ty.getAppFnArgs with
    | ``And, 0, (_, #[a, b]) => interp (mkApp3 (mkConst ``And.left) a b e)
    | ``And, 1, (_, #[a, b]) => interp (mkApp3 (mkConst ``And.right) a b e)
    | ``Iff, 0, (_, #[a, b]) => interp (mkApp3 (mkConst ``Iff.mp) a b e)
    | ``Iff, 1, (_, #[a, b]) => interp (mkApp3 (mkConst ``Iff.mpr) a b e)
    | _, _, _ => throwError "transform: projection {t} is not handled"
  | .app .. | .const .. => interpApp t.getAppFn t.getAppArgs
  | _ => throwError "transform: proof term of an unexpected form: {t}"

/-- `fun K => λv̄. ∀u. K v̄ u`, for working under a quantifier by congruence. `u` must be the
last variable in scope one level down. -/
partial def underForall (u : Expr) : TrM Expr := do
  let T' ← withReader (fun c => { c with vars := c.vars.push u }) (return (← algebra).1)
  withLocalDeclD `K T' fun k => do
    let vs := (← read).vars
    mkLambdaFVars #[k] (← lamV (← mkForallFVars #[u] (mkAppN k (vs.push u))))

/-- A binder type that is a type or a class, as opposed to an `R`-type of objects. -/
partial def isParam' (d : Expr) : TrM Bool := do
  let d ← whnf d
  -- `Prop` is the type `t` of `R`, whose inhabitants are objects; any other sort is a
  -- universe of types
  if let .sort l := d then return !l.isZero
  return (← isClass? d).isSome

/-- A hypothesis in scope: `rule_hyp` where it was introduced, weakened past the rest. -/
partial def interpHyp (id : FVarId) : TrM (Expr × Expr) := do
  let hyps := (← read).hyps
  let some i := hyps.findIdx? (·.1 == id)
    | throwError "transform: {mkFVar id} is not a hypothesis in scope. Inside a gated \
`propext` or `funext` no outer hypothesis may be used; that is the gate."
  let Γs ← gammas
  let Hi ← lamV hyps[i]!.2
  let mut pf ← rule ``Classicism.Strict.BA.rule_hyp #[← lamV Γs[i]!, Hi]
  for j in [i+1:hyps.size] do
    pf ← rule ``Classicism.Strict.BA.rule_weaken #[← lamV Γs[j]!, Hi, ← lamV hyps[j]!.2, pf]
  return (hyps[i]!.2, pf)

/-- An identity `(λv̄. got) = (λv̄. exp)` between two readings of what Lean regards as one
formula. Identical up to unfolding: `rfl`. Boolean-equivalent, as `¬A` and `A → ⊥` are: the
tautology tactic, between λ-terms. Otherwise by congruence on a shared outer connective or
quantifier, which is Leibniz's Law. -/
partial def bridge (got exp : Expr) : TrM Expr := do
  if ← isDefEq got exp then return ← mkEqRefl (← lamV got)
  -- instantiating a family such as Leibniz's Law leaves β-redexes, which hide the shape
  let got ← Core.betaReduce got
  let exp ← Core.betaReduce exp
  try
    return ← Classicism.Strict.proveBooleanEq (← lamV got) (← lamV exp)
  catch _ => pure ()
  -- abbreviations such as `◇` may hide the Boolean shape
  let got' ← whnfR got
  let exp' ← whnfR exp
  if got' != got || exp' != exp then
    try
      return ← Classicism.Strict.proveBooleanEq (← lamV got') (← lamV exp')
    catch _ => pure ()
  match got', exp' with
  | .forallE nm d b _, .forallE _ d₂ b₂ _ =>
    if !(← isProp d) && (← isDefEq d d₂) then
      return ← withLocalDeclD nm d fun u => do
        let E ← withReader (fun c => { c with vars := c.vars.push u })
          (bridge (b.instantiate1 u) (b₂.instantiate1 u))
        mkCongrArg (← underForall u) E
  | _, _ => pure ()
  match got'.getAppFnArgs, exp'.getAppFnArgs with
  | (``Exists, #[σ, .lam nm _ b _]), (``Exists, #[_, .lam _ _ b₂ _]) =>
    return ← withLocalDeclD nm σ fun u => do
      let E ← withReader (fun c => { c with vars := c.vars.push u })
        (bridge (b.instantiate1 u) (b₂.instantiate1 u))
      let T' ← withReader (fun c => { c with vars := c.vars.push u }) (return (← algebra).1)
      let m ← withLocalDeclD `K T' fun k => do
        let vs := (← read).vars
        let body ← mkLambdaFVars #[u] (mkAppN k (vs.push u))
        mkLambdaFVars #[k] (← lamV (mkApp2 (mkConst ``Exists [Level.one]) σ body))
      mkCongrArg m E
  | (f, as), (f₂, as₂) =>
    if f == f₂ && as.size == as₂.size && as.size > 0 then
      -- the same connective: congruence in each argument that differs
      let (T, _) ← algebra
      let mut cur := as
      let mut E ← mkEqRefl (← lamV got')
      for i in [0:as.size] do
        if ← isDefEq as[i]! as₂[i]! then continue
        unless ← isProp as[i]! do
          throwError "transform: cannot bridge{indentExpr got}\nand{indentExpr exp}"
        let Ei ← bridge as[i]! as₂[i]!
        let here := cur
        let m ← withLocalDeclD `K T fun k => do
          let vs := (← read).vars
          mkLambdaFVars #[k] (← lamV (mkAppN got'.getAppFn (here.set! i (mkAppN k vs))))
        E ← mkEqTrans E (← mkCongrArg m Ei)
        cur := cur.set! i as₂[i]!
      return E
    throwError "transform: cannot bridge{indentExpr got}\nand{indentExpr exp}"

/-- Use a proof of `Γ ⊩ got` at the formula `exp`. -/
partial def coerce (pf got exp : Expr) : TrM Expr := do
  if ← isDefEq got exp then return pf
  let E ← bridge got exp
  let (T, inst) ← algebra
  let G ← lamV (← gamma)
  let m ← withLocalDeclD `K T fun k => do
    mkLambdaFVars #[k] (mkAppN (mkConst ``Classicism.Strict.BA.Seq) #[T, inst, G, k])
  mkEqMP (← mkCongrArg m E) pf

/-- An application. The head is transformed first, as a constant with its type arguments or
as a hypothesis, and the remaining arguments are then fed to it one at a time. -/
partial def interpApp (f : Expr) (args : Array Expr) : TrM (Expr × Expr) := do
  if let .const c ls := f then
    if let some t' ← restate c ls args then return ← interp t'
    if c == ``propext || c == ``funext then
      let n := if c == ``propext then 3 else 5
      let site := mkAppN f (args.extract 0 n)
      let E ← withReader (fun ctx => { ctx with hyps := #[] }) (interpEq site)
      let (F, pf) ← seqOfEq site E
      return ← feed F pf (args.extract n args.size)
    -- a constant: cite its necessitation at its type arguments
    let mut k := 0
    for a in args do
      if ← isParam a then k := k + 1 else break
    let params := args.extract 0 k
    let necN ← necFor c
    let mut necPf := mkAppN (mkConst necN) (← params.mapM translate)
    -- the necessitation may ask for `Ty` evidence the core constant did not
    repeat
      let ty ← whnf (← inferType necPf)
      match ty with
      | .forallE _ d _ .instImplicit => necPf := mkApp necPf (← synthInstance d)
      | _ => break
    let some (_, S, _) := (← inferType necPf).eq?
      | throwError "transform: {necN} is not of the form `S = ⊤`"
    let m ← withLocalDeclD `r propE fun r => do mkLambdaFVars #[r] (← lamV r)
    let pf ← rule ``Classicism.Strict.BA.rule_const #[← lamV (← gamma), ← lamV S, ← mkCongrArg m necPf]
    return ← feed S pf (args.extract k args.size)
  let (F, pf) ← interp f
  feed F pf args

/-- Put a formula into a shape that says what it can be applied to: `imp A B`, `¬A`, or
`∀x. B`. Definitions are unfolded one at a time until one of those appears. -/
partial def expose (F : Expr) : TrM Expr := do
  let F ← whnfCore F
  match F.getAppFnArgs with
  | (``Classicism.imp, #[_, _]) => return F
  | (``Not, #[_]) => return F
  | _ =>
    if F.isForall then return F
    match ← unfoldDefinition? F with
    | some F' => expose F'
    | none => throwError "transform: a proof of{indentExpr F}\nis applied to an argument"

/-- Feed arguments to a transformed head whose formula is `F`. The shape of `F` says whether
the next argument is a proof (modus ponens) or a term (`UI`). -/
partial def feed (F : Expr) (pf : Expr) (args : Array Expr) : TrM (Expr × Expr) := do
  let mut F := F
  let mut pf := pf
  let G ← lamV (← gamma)
  for a in args do
    F ← expose F
    match F.getAppFnArgs with
    | (``Classicism.imp, #[A, B]) =>
      -- modus ponens: Appendix A, inductive step (i)
      let (got, pa) ← interp a
      let pa ← coerce pa got A
      pf ← rule ``Classicism.Strict.BA.rule_imp_elim #[G, ← lamV A, ← lamV B, pf, pa]
      F := B
    | (``Not, #[A]) =>
      let (got, pa) ← interp a
      let pa ← coerce pa got A
      pf ← rule ``Classicism.Strict.BA.rule_not_elim #[G, ← lamV A, pf, pa]
      F := mkConst ``Classicism.Strict.Bot
    | _ =>
      let .forallE nm d b _ := F | throwError "transform: internal error in feed"
      if ← isProp d then
        throwError "transform: a formula depends on a proof:{indentExpr F}"
      -- `UI`: Appendix A, base case (ii)
      let inst ← tyInst d
      let Bfun := Expr.lam nm d b .default
      let a' ← translate a
      let ax := mkApp2 (mkConst ``Classicism.Axiomatic.absorption_or_forall) d inst
      let ha ← liftClosed ax #[Bfun, a']
      pf ← rule ``Classicism.Strict.BA.rule_absorb #[G, ← lamV (b.instantiate1 a'), ← lamV F, ha, pf]
      F := b.instantiate1 a'
  return (F, pf)

/-- The necessitation of a constant: hand-proved for a core constant, and for a library
theorem its own transform, made on demand. -/
partial def necFor (c : Name) : TrM Name := do
  let env ← getEnv
  if let some n := (necExt.getState env).find? c then return n
  if env.contains (primNecName c) then return primNecName c
  if (`Classicism).isPrefixOf c then
    if let some pinfo ← getProjectionFnInfo? c then
      if pinfo.fromClass then
        throwError "transform: {c} is a law field of a class, and the class has no strict \
mirror yet"
    if let some (.thmInfo _) := env.find? c then
      ensureNec c
      return necName c
  throwError "transform: no necessitation is known for the constant {c}"

/-- Restate a use of a core constant so that its type is a formula: recursors get their
motives instantiated, and the identity lemmas are routed through Leibniz's Law. -/
partial def restate (c : Name) (ls : List Level) (args : Array Expr) : TrM (Option Expr) := do
  let prim (n : Name) (σs : Array Expr) (rest : Array Expr) : TrM (Option Expr) := do
    let mut h := mkAppN (mkConst n) σs
    repeat
      match ← whnf (← inferType h) with
      | .forallE _ d _ .instImplicit => h := mkApp h (← synthInstance d)
      | _ => break
    return some (mkAppN h rest)
  -- the property a motive `fun z (_ : a = z) => P z` stands for
  let motiveProp (motive : Expr) (arity : Nat) : TrM Expr := do
    forallBoundedTelescope (← inferType motive) arity fun xs _ => do
      let body := (motive.beta xs).headBeta
      if arity == 2 then
        if body.containsFVar xs[1]!.fvarId! then
          throwError "transform: a motive depends on the identity proof: {motive}"
      unless ← isProp body do
        throwError "transform: a recursor eliminates into data, not a proposition: {motive}"
      mkLambdaFVars #[xs[0]!] body
  -- the goal a motive yields at the major premise, which by proof irrelevance is its value
  let goalOf (motive major : Expr) : TrM Expr := do
    let C := (motive.beta #[major]).headBeta
    unless ← isProp C do
      throwError "transform: a recursor eliminates into data, not a proposition: {motive}"
    return C
  let rest (n : Nat) : Array Expr := args.extract n args.size
  match c with
  | ``rfl => if args.size ≥ 2 then return some (mkAppN (mkConst ``Eq.refl ls) args) else return none
  | ``Eq.rec =>
    if args.size < 6 then return none
    let P ← motiveProp args[2]! 2
    let r ← prim ``Classicism.Strict.Prim.ll #[args[0]!] #[args[1]!, args[4]!, P, args[5]!, args[3]!]
    return r.map (mkAppN · (rest 6))
  | ``Eq.ndrec =>
    if args.size < 6 then return none
    let P ← motiveProp args[2]! 1
    let r ← prim ``Classicism.Strict.Prim.ll #[args[0]!] #[args[1]!, args[4]!, P, args[5]!, args[3]!]
    return r.map (mkAppN · (rest 6))
  | ``And.casesOn =>
    if args.size < 5 then return none
    let C ← goalOf args[2]! args[3]!
    return some (mkAppN (mkConst ``Classicism.Strict.Prim.and_rec)
      (#[args[0]!, args[1]!, C, args[4]!, args[3]!] ++ rest 5))
  | ``And.rec =>
    if args.size < 5 then return none
    let C ← goalOf args[2]! args[4]!
    return some (mkAppN (mkConst ``Classicism.Strict.Prim.and_rec)
      (#[args[0]!, args[1]!, C, args[3]!, args[4]!] ++ rest 5))
  | ``Or.casesOn =>
    if args.size < 6 then return none
    let C ← goalOf args[2]! args[3]!
    return some (mkAppN (mkConst ``Classicism.Strict.Prim.or_rec)
      (#[args[0]!, args[1]!, C, args[4]!, args[5]!, args[3]!] ++ rest 6))
  | ``Or.rec =>
    if args.size < 6 then return none
    let C ← goalOf args[2]! args[5]!
    return some (mkAppN (mkConst ``Classicism.Strict.Prim.or_rec)
      (#[args[0]!, args[1]!, C, args[3]!, args[4]!, args[5]!] ++ rest 6))
  | ``Exists.casesOn =>
    if args.size < 5 then return none
    let C ← goalOf args[2]! args[3]!
    let r ← prim ``Classicism.Strict.Prim.exists_rec #[args[0]!] #[args[1]!, C, args[4]!, args[3]!]
    return r.map (mkAppN · (rest 5))
  | ``Exists.rec =>
    if args.size < 5 then return none
    let C ← goalOf args[2]! args[4]!
    let r ← prim ``Classicism.Strict.Prim.exists_rec #[args[0]!] #[args[1]!, C, args[3]!, args[4]!]
    return r.map (mkAppN · (rest 5))
  | ``Exists.elim =>
    -- `Exists.elim {α} {p} {b} (h : ∃ x, p x) (f : ∀ a, p a → b) : b`
    if args.size < 5 then return none
    let r ← prim ``Classicism.Strict.Prim.exists_rec #[args[0]!] #[args[1]!, args[2]!, args[4]!, args[3]!]
    return r.map (mkAppN · (rest 5))
  | ``False.rec | ``False.casesOn =>
    if args.size < 2 then return none
    let C ← goalOf args[0]! args[1]!
    return some (mkAppN (mkConst ``Classicism.Strict.Prim.false_rec) (#[C, args[1]!] ++ rest 2))
  | ``Eq.symm => if args.size ≥ 1 then prim ``Classicism.Strict.Prim.eq_symm #[args[0]!] (rest 1) else return none
  | ``Eq.trans => if args.size ≥ 1 then prim ``Classicism.Strict.Prim.eq_trans #[args[0]!] (rest 1) else return none
  | ``Eq.subst => if args.size ≥ 1 then prim ``Classicism.Strict.Prim.eq_subst #[args[0]!] (rest 1) else return none
  | ``Eq.mpr => return some (mkAppN (mkConst ``Classicism.Strict.Prim.eq_mpr) args)
  | ``Eq.mp => return some (mkAppN (mkConst ``Classicism.Strict.Prim.eq_mp) args)
  | ``congrArg =>
    if args.size ≥ 2 then prim ``Classicism.Strict.Prim.congr_arg #[args[0]!, args[1]!] (rest 2)
    else return none
  | ``congrFun =>
    -- `β` is a type family; only the constant family is a type of `R`
    if args.size < 2 then return none
    let .lam _ _ ρ _ := args[1]! | return none
    if ρ.hasLooseBVars then throwError "transform: `congrFun` at a dependent function type"
    prim ``Classicism.Strict.Prim.congr_fun #[args[0]!, ρ] (rest 2)
  | ``Trans.trans =>
    -- `calc` steps between identities
    if args.size ≥ 12 then
      if args[6]!.isAppOf ``instTransEq then
        return ← prim ``Classicism.Strict.Prim.eq_trans #[args[0]!] (rest 7)
    return none
  | _ =>
    -- a compiled `match`: unfold it to the recursor it abbreviates; likewise the core
    -- lemmas `simp` leaves in a proof term, whose bodies are `propext`, `funext`, `Eq.rec`
    -- and `Iff.intro` on their arguments (the gate has checked that the hypothesis
    -- argument of `eq_true`, `eq_false` and `forall_congr` is closed, so after unfolding
    -- the gated site is `propext` or `funext` at a closed argument, as usual)
    if coreUnfolded.contains c || (← isMatcher c) then
      let info ← getConstInfo c
      let v := (info.value! (allowOpaque := true)).instantiateLevelParams info.levelParams ls
      return some (v.beta args).headBeta
    return none

/-- The λ-level identity a gated site proves. `t : a = b` mentions no hypothesis, so it is
transformed with `Γ` empty, and the result is a proof of `(λv̄. a') = (λv̄. b')`: the rule of
Equivalence in the bundled form the paper states it in. -/
partial def interpEq (t : Expr) : TrM Expr := do
  let t := (← instantiateMVars t).consumeMData.headBeta
  -- Proposition A.3, from a transformed proof of the biconditional
  let ofIff (a b s : Expr) : TrM Expr := do
    let a' ← translate a
    let b' ← translate b
    let iffF := mkApp2 (mkConst ``Classicism.iff) a' b'
    let (got, ps) ← interp s
    let ps ← coerce ps got iffF
    let h ← rule ``Classicism.Strict.BA.of_seq_top #[← lamV iffF, ps]
    rule ``Classicism.Strict.BA.eq_of_iff_top #[← lamV a', ← lamV b', h]
  match t.getAppFnArgs with
  | (``propext, #[a, b, s]) => ofIff a b s
  | (``funext, #[α, _, _, _, s]) =>
    -- ζ: the bound variable joins `v̄`, and η identifies `λv̄x. f x` with `λv̄. f`
    withLocalDeclD `x α fun x => do
      withReader (fun c => { c with vars := c.vars.push x }) (interpEq (mkApp s x).headBeta)
  | _ =>
    -- any other closed proof of an identity between propositions: `a = b` gives `a ↔ b` by
    -- Leibniz's Law, and then Proposition A.3 again
    let some (ρ, a, b) := (← whnf (← inferType t)).eq? | throwError "transform: {t} is not an identity"
    unless (← whnf ρ).isProp do
      throwError "transform: a gated `funext` whose body is an identity at {ρ}, not at `Prop`, \
is not yet handled"
    ofIff a b (mkApp3 (mkConst ``Classicism.Strict.Prim.iff_of_eq) a b t)

/-- From the λ-level identity `E : (λv̄. a') = (λv̄. b')` to the sequent `Γ ⊩ a' = b'`:
substitute in `a' = a'`, which is `⊤` by `Ref`. Appendix A, base case (viii). -/
partial def seqOfEq (site E : Expr) : TrM (Expr × Expr) := do
  let some (ρ, a, b) := (← whnf (← inferType site)).eq? | throwError "transform: {site} is not an identity"
  let a' ← translate a
  let b' ← translate b
  let inst ← tyInst ρ
  let Γ ← gamma
  let some (Tρ, _, _) := (← inferType E).eq? | throwError "transform: internal error in seqOfEq"
  let vs := (← read).vars
  let m ← withLocalDeclD `K Tρ fun k => do
    let eq ← mkEq a' (mkAppN k vs)
    mkLambdaFVars #[k] (← lamV (mkApp2 (mkConst ``Classicism.imp) Γ eq))
  let c ← mkCongrArg m E
  let refl ← liftClosed (mkApp2 (mkConst ``Classicism.Strict.ref_lam) ρ inst) #[a']
  let pfRefl ← rule ``Classicism.Strict.BA.rule_const #[← lamV Γ, ← lamV (← mkEq a' a'), refl]
  return (← mkEq a' b', ← mkEqTrans (← mkEqSymm c) pfRefl)

/-- The parameters of a theorem, with each one whose type reads differently, such as
`inst : Rel τ`, replaced by a fresh variable of the mirrored type, `inst' : SRel τ`. -/
partial def withMirroredParams {α : Type} (xs : List Expr) (acc : Array Expr)
    (k : Array Expr → TrM α) : TrM α := do
  match xs with
  | [] => k acc
  | x :: rest =>
    let decl ← x.fvarId!.getDecl
    let ty' ← translate decl.type
    if ty' == decl.type then withMirroredParams rest (acc.push x) k
    else
      withLocalDecl decl.userName decl.binderInfo ty' fun y =>
        withReader (fun c => { c with subst := c.subst.insert x.fvarId! y })
          (withMirroredParams rest (acc.push y) k)

/-- Make `c.nec` and `c.strict`, unless they exist. -/
partial def ensureNec (c : Name) : TrM Unit := do
  if (← getEnv).contains (necName c) then return
  if (← get).inProgress.contains c then throwError "transform: {c} depends on itself"
  let .thmInfo info ← getConstInfo c | throwError "transform: {c} is not a theorem"
  modify fun s => { s with inProgress := s.inProgress.insert c }
  -- type and instance parameters stay parameters: the theorem is a family indexed by them
  let k ← leadingParams info.type
  let (necTy, necVal, strictTy, strictVal) ←
    forallBoundedTelescope info.type (some k) fun xs stmt => do
      let body := (info.value.beta xs).headBeta
      withReader (fun _ => {}) <| withMirroredParams xs.toList #[] fun ys => do
        let (got, pf) ← interp body
        let S ← translate stmt
        let pf ← coerce pf got S
        let pf ← rule ``Classicism.Strict.BA.of_seq_top #[S, pf]
        let necTy ← mkForallFVars ys (← mkEq S topP)
        let necVal ← mkLambdaFVars ys pf
        let strictTy ← mkForallFVars ys S
        let strictVal ← mkLambdaFVars ys
          (mkApp2 (mkConst ``Classicism.Strict.of_eq_top) S (mkAppN (mkConst (necName c)) ys))
        return (necTy, necVal, strictTy, strictVal)
  -- checked synchronously, so that a rejected proof is an error here rather than later
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := necName c, levelParams := [], type := necTy, value := necVal })
    addDecl (.thmDecl { name := strictName c, levelParams := [], type := strictTy, value := strictVal })
  modify fun s => { s with inProgress := s.inProgress.erase c }

/-- How many leading binders of a statement are types or instances. -/
partial def leadingParams (ty : Expr) : TrM Nat :=
  forallTelescope ty fun xs _ => do
    let mut k := 0
    for x in xs do
      if ← isParam' (← inferType x) then k := k + 1 else break
    return k

end

/-- Run the transformer on one theorem. -/
def transform (c : Name) : MetaM Unit := do
  ((ensureNec c).run {}).run' {}

/-! ### Commands -/

/-- `#classicism_transform foo …` transforms each named theorem, declaring `foo.nec` and
`foo.strict`, and reports the axioms the result rests on. -/
syntax (name := classicismTransform) "#classicism_transform " ident+ : command

@[command_elab classicismTransform] def elabTransform : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      liftTermElabM (transform n)
    catch ex =>
      logError m!"{n}: not transformed — {ex.toMessageData}"
      continue
    let ax ← liftTermElabM (collectAxioms (strictName n))
    let bad := ax.filter (fun a => !strictAllowedAxiom a)
    if bad.isEmpty then
      let ty := ((← getEnv).find? (strictName n)).map (·.type)
      logInfo m!"{n} ⟶ {strictName n} : {ty.getD default}\nstrict ✓ (axioms: {ax.toList})"
    else
      logError m!"{n} ⟶ {strictName n}: still depends on {bad.toList}"

/-- `#classicism_mirror a b` records that `b` is the strict mirror of the constant `a`: a
class, one of its data projections, or one of its instances. -/
syntax (name := classicismMirror) "#classicism_mirror " ident ident : command

@[command_elab classicismMirror] def elabMirror : CommandElab := fun stx => do
  let a ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let b ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[2])
  modifyEnv (mirrorExt.addEntry · (a, b))

/-- `#classicism_nec a b` records that the theorem `b : S' = ⊤` is the necessitation of the
constant `a : S`, for a constant whose necessitation cannot be made by transforming it: a
law field of a class. -/
syntax (name := classicismNec) "#classicism_nec " ident ident : command

@[command_elab classicismNec] def elabNec : CommandElab := fun stx => do
  let a ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let b ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[2])
  modifyEnv (necExt.addEntry · (a, b))

/-- `#classicism_transform_audit Mod₁ …` transforms every theorem declared in the named
modules and reports how many came out strict, with the reason for each that did not. -/
syntax (name := classicismTransformAudit) "#classicism_transform_audit " ident+ : command

@[command_elab classicismTransformAudit] def elabTransformAudit : CommandElab := fun stx => do
  for modId in stx[1].getArgs do
    let env ← getEnv
    let some idx := env.getModuleIdx? modId.getId
      | logError m!"no module {modId.getId}"; continue
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .thmInfo _ := ci then
          -- a law field of a class is a projection, not a proof; its necessitation is the
          -- mirror's, registered by `#classicism_nec`
          let isProj := (← liftCoreM (getProjectionFnInfo? n)).isSome
          if !n.isInternalDetail && !isProj then names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    let mut ok : Nat := 0
    let mut failures : Array MessageData := #[]
    for n in names do
      try
        liftTermElabM (transform n)
        let ax ← liftTermElabM (collectAxioms (strictName n))
        if ax.all strictAllowedAxiom then ok := ok + 1
        else failures := failures.push m!"{n}: result depends on {(ax.filter (!strictAllowedAxiom ·)).toList}"
      catch ex =>
        failures := failures.push m!"{n}: {ex.toMessageData}"
    logInfo m!"{modId.getId}: {ok} of {names.size} theorems transformed\n\
{MessageData.joinSep failures.toList "\n"}"

end Classicism.Check
