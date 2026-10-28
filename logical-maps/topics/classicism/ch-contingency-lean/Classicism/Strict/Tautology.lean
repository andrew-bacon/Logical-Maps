import Lean
import Classicism.Strict.Vocabulary

/-!
# `boolean_eq`: deciding propositional identities strictly

This is the propositional case of Appendix A, as a tactic. Given a goal `P = Q` where `P`
and `Q` are built from propositional atoms by `∧`, `∨`, `¬`, `⊤` and `⊥`, and are
tautologically equivalent, `boolean_eq` produces a proof **from the six Boolean Identities
alone**. It emits no `propext`, no `funext`, and no `em`, so `#classicism_strict` accepts
everything it builds. If `P` and `Q` are not equivalent it reports a falsifying assignment.

## The method: Shannon expansion

The recursion is on the list of atoms, and it is driven by the cancellation lemma already
in `Classicism/Strict.lean`,

    eq_of_meet_eq :  (a ∧ P) = (a ∧ Q)  →  (¬a ∧ P) = (¬a ∧ Q)  →  P = Q

which is where associativity came from too. To prove `P = Q`, pick an atom `a` and prove
the two conjoined equations. Each of those is settled by *substituting for `a`*: under the
conjunct `a` the formula `P` may have every occurrence of `a` replaced by `⊤`, and under
`¬a` by `⊥`. That is `substLit` below, and it leaves a formula with one fewer atom, so the
recursion terminates. With no atoms left, a formula is built from `⊤` and `⊥` only, and
`evalClosed` collapses it to one of them by the bound laws.

So the shape of a produced proof, for atoms `a, b`, is a binary tree of depth two whose
four leaves are each `⊤ = ⊤` or `⊥ = ⊥`. That is exponential in the number of atoms, which
is the right cost for a complete method and no trouble at the sizes that occur here.

## Why substitution needs a lemma about negation

`substLit` recurses on the formula. Conjunction and disjunction are easy, because a
conjunct distributes into both: `meet_meet_split` and `meet_join_distrib`. Negation is the
interesting case, since from `l ∧ Q = l ∧ Q'` one cannot simply conclude
`l ∧ ¬Q = l ∧ ¬Q'` by congruence. The bridge is `relative_compl`,

    l ∧ ¬q  =  l ∧ ¬(l ∧ q)

which says that under `l` the complement of `q` and of `l ∧ q` agree, so the recursive
equation can be applied inside and then the lemma used again in reverse.

## How a tactic is put together

Three layers, each a plain function in `MetaM` returning a *proof term*:

* `evalClosed e` returns which bound `e` is, and a proof of `e = ⊤` or `e = ⊥`.
* `substLit` returns the substituted formula and a proof of `l ∧ P = l ∧ P'`.
* `proveEq` ties them together with `eq_of_meet_eq`.

Nothing here is trusted. `proveEq` hands the kernel a term, and if any of this code is
wrong the term fails to typecheck and the tactic errors; it cannot produce a false theorem.
The front end `boolean_eq` reads the goal, collects the atoms and assigns the result.
-/

open Lean Meta Elab Tactic

namespace Classicism.Strict

/-! ### Building and taking apart formulas

The tactic works in any algebra `BA τ` of `Classicism/Algebra.lean`, so the same code
decides identities between propositions and identities between λ-terms of type
`v̄ → Prop`. The algebra is carried in a reader. -/

/-- The algebra a run of the tactic works in: the carrier `τ` and its `BA τ` instance. A
plain pair, not a structure, so that no auxiliary theorems are generated for the audits of
this module to trip over. -/
abbrev Alg := Expr × Expr

/-- The tactic's monad. -/
abbrev BM := ReaderT Alg MetaM

private def op (n : Name) (args : Array Expr) : BM Expr := do
  let a ← read
  return mkAppN (mkConst n) (#[a.1, a.2] ++ args)

private def mkMeet (p q : Expr) : BM Expr := op ``BA.and #[p, q]
private def mkJoin (p q : Expr) : BM Expr := op ``BA.or #[p, q]
private def mkCompl (p : Expr) : BM Expr := op ``BA.neg #[p]
private def topE : BM Expr := op ``BA.top #[]
private def botE : BM Expr := op ``BA.bot #[]
/-- A law of `Classicism/Algebra.lean`, applied to elements. -/
private def law (n : Name) (args : Array Expr) : BM Expr := op n args

/-- `fun x : τ => body x`, for congruence steps. -/
private def ctxLam (body : Expr → BM Expr) : BM Expr := do
  let a ← read
  withLocalDeclD `x a.1 fun x => do mkLambdaFVars #[x] (← body x)

private def isUnit (e : Expr) : Bool :=
  e.isAppOf ``BA.unit || e.isConstOf ``Classicism.Strict.everything

/-- Put a formula into the canonical vocabulary `BA.and`, `BA.or`, `BA.neg`, `BA.top`,
`BA.bot`. At `Prop` this reads Lean's `∧`, `∨`, `¬` and the paper's `⊤`, `⊥`, `imp`, `iff`;
at any algebra it unfolds `BA.imp` and `BA.iff`. The result is definitionally equal to the
input, so a proof about it is accepted against the original goal with no bridging lemma.
Lean's own `→` and `Iff` are deliberately *not* read: they are not Boolean combinations,
and a goal mentioning them has its arrow or `Iff` treated as an atom. -/
partial def reify (e : Expr) : BM Expr := do
  let e := e.consumeMData
  -- a local definition `let X := …` is transparent
  if let .fvar id := e then
    if let some v ← id.getValue? then return ← reify v
  let bin (mk : Expr → Expr → BM Expr) (p q : Expr) : BM Expr := do mk (← reify p) (← reify q)
  let imp (p q : Expr) : BM Expr := do mkJoin (← mkCompl (← reify p)) (← reify q)
  let iff (p q : Expr) : BM Expr := do
    let p' ← reify p
    let q' ← reify q
    mkMeet (← mkJoin (← mkCompl p') q') (← mkJoin (← mkCompl q') p')
  -- the bounds, folded or unfolded
  let isBound (args : Array Expr) : Bool :=
    args.size == 2 && isUnit args[0]! &&
      (match args[1]!.getAppFnArgs with
       | (``Not, #[u]) => isUnit u
       | (``BA.neg, #[_, _, u]) => isUnit u
       | _ => false)
  match e.getAppFnArgs with
  | (``Classicism.Strict.Top, _) => topE
  | (``Classicism.Strict.Bot, _) => botE
  | (``BA.top, _) => topE
  | (``BA.bot, _) => botE
  | (``And, #[p, q]) => if isBound #[p, q] then botE else bin mkMeet p q
  | (``Or, #[p, q]) => if isBound #[p, q] then topE else bin mkJoin p q
  | (``Not, #[p]) => do mkCompl (← reify p)
  | (``BA.and, #[_, _, p, q]) => if isBound #[p, q] then botE else bin mkMeet p q
  | (``BA.or, #[_, _, p, q]) => if isBound #[p, q] then topE else bin mkJoin p q
  | (``BA.neg, #[_, _, p]) => do mkCompl (← reify p)
  | (``Classicism.imp, #[p, q]) => imp p q
  | (``Classicism.iff, #[p, q]) => iff p q
  | (``BA.imp, #[_, _, p, q]) => imp p q
  | (``BA.iff, #[_, _, p, q]) => iff p q
  | _ =>
    -- Not an operation of this algebra as written. If the algebra is `v̄ → Prop`, the
    -- element may still be one *pointwise*: `fun v̄ => A ∧ B` is `BA.and (fun v̄ => A)
    -- (fun v̄ => B)` by β. Look under the binders and re-abstract the parts.
    let (ty, _) ← read
    if !ty.isForall then return e
    forallTelescope ty fun xs _ => do
      let body := (e.beta xs).consumeMData
      let lam (p : Expr) : BM Expr := do reify (← mkLambdaFVars xs p).eta
      let bin' (mk : Expr → Expr → BM Expr) (p q : Expr) : BM Expr := do mk (← lam p) (← lam q)
      let imp' (p q : Expr) : BM Expr := do mkJoin (← mkCompl (← lam p)) (← lam q)
      let iff' (p q : Expr) : BM Expr := do
        let p' ← lam p
        let q' ← lam q
        mkMeet (← mkJoin (← mkCompl p') q') (← mkJoin (← mkCompl q') p')
      match body.getAppFnArgs with
      | (``Classicism.Strict.Top, _) => topE
      | (``Classicism.Strict.Bot, _) => botE
      | (``BA.top, #[_, _]) => topE
      | (``BA.bot, #[_, _]) => botE
      | (``And, #[p, q]) => if isBound #[p, q] then botE else bin' mkMeet p q
      | (``Or, #[p, q]) => if isBound #[p, q] then topE else bin' mkJoin p q
      | (``Not, #[p]) => do mkCompl (← lam p)
      | (``BA.and, #[_, _, p, q]) => if isBound #[p, q] then botE else bin' mkMeet p q
      | (``BA.or, #[_, _, p, q]) => if isBound #[p, q] then topE else bin' mkJoin p q
      | (``BA.neg, #[_, _, p]) => do mkCompl (← lam p)
      | (``Classicism.imp, #[p, q]) => imp' p q
      | (``Classicism.iff, #[p, q]) => iff' p q
      | (``BA.imp, #[_, _, p, q]) => imp' p q
      | (``BA.iff, #[_, _, p, q]) => iff' p q
      | _ => return e

/-- The atoms of a canonical formula: every maximal subterm that is not an operation. -/
partial def atomsOf (e : Expr) (acc : Array Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``BA.and, #[_, _, p, q]) => atomsOf q (atomsOf p acc)
  | (``BA.or, #[_, _, p, q]) => atomsOf q (atomsOf p acc)
  | (``BA.neg, #[_, _, p]) => atomsOf p acc
  | (``BA.top, _) => acc
  | (``BA.bot, _) => acc
  | _ => if acc.any (· == e) then acc else acc.push e

/-! ### Layer one: atom-free formulas -/

/-- Collapse a formula built only from `⊤` and `⊥`. Returns `true` for `⊤`, together with
a proof of `e = ⊤`, and `false` with a proof of `e = ⊥`. Every step is one of the bound
laws of `Classicism/Algebra.lean`. -/
partial def evalClosed (e : Expr) : BM (Bool × Expr) := do
  let bound (v : Bool) : BM Expr := if v then topE else botE
  match e.getAppFnArgs with
  | (``BA.top, _) => return (true, ← mkEqRefl (← topE))
  | (``BA.bot, _) => return (false, ← mkEqRefl (← botE))
  | (``BA.neg, #[_, _, p]) =>
    let (v, hp) ← evalClosed p
    -- `∼p = ∼(bound) = the other bound`
    let step ← mkCongrArg (← ctxLam fun x => mkCompl x) hp
    let close ← law (if v then ``BA.compl_top else ``BA.compl_bot) #[]
    return (!v, ← mkEqTrans step close)
  | (``BA.and, #[_, _, p, q]) =>
    let (vp, hp) ← evalClosed p
    let (vq, hq) ← evalClosed q
    let step₁ ← mkCongrArg (← ctxLam fun x => mkMeet x q) hp
    let step₂ ← mkCongrArg (← ctxLam fun x => do mkMeet (← bound vp) x) hq
    -- now `(bound) ⊓ (bound)`; pick the law that collapses it
    let close ← law (if vp then ``BA.top_meet else ``BA.bot_meet) #[← bound vq]
    return (vp && vq, ← mkEqTrans (← mkEqTrans step₁ step₂) close)
  | (``BA.or, #[_, _, p, q]) =>
    let (vp, hp) ← evalClosed p
    let (vq, hq) ← evalClosed q
    let step₁ ← mkCongrArg (← ctxLam fun x => mkJoin x q) hp
    let step₂ ← mkCongrArg (← ctxLam fun x => do mkJoin (← bound vp) x) hq
    let close ← law (if vp then ``BA.top_join else ``BA.bot_join) #[← bound vq]
    return (vp || vq, ← mkEqTrans (← mkEqTrans step₁ step₂) close)
  | _ => throwError "boolean_eq: {e} still contains an atom"

/-! ### Layer two: substituting for one atom -/

/-- Under the literal `l`, replace every occurrence of the atom `a` in `P` by `v`.
`l` is `a` itself with `v = ⊤`, or `∼a` with `v = ⊥`. Returns the substituted formula and
a proof of `l ⊓ P = l ⊓ P'`. -/
partial def substLit (l a v : Expr) (pos : Bool) (P : Expr) : BM (Expr × Expr) := do
  if P == a then
    -- the atom itself: `a ⊓ a = a ⊓ ⊤`, or `∼a ⊓ a = ∼a ⊓ ⊥`
    let lem := if pos then ``BA.meet_self_eq_meet_top else ``BA.compl_meet_eq_meet_bot
    return (v, ← law lem #[a])
  match P.getAppFnArgs with
  | (``BA.and, #[_, _, p, q]) =>
    let (p', hp) ← substLit l a v pos p
    let (q', hq) ← substLit l a v pos q
    -- `l ⊓ (p ⊓ q) = (l⊓p) ⊓ (l⊓q) = (l⊓p') ⊓ (l⊓q') = l ⊓ (p' ⊓ q')`
    let split ← law ``BA.meet_meet_split #[l, p, q]
    let r₁ ← mkCongrArg (← ctxLam fun x => do mkMeet x (← mkMeet l q)) hp
    let r₂ ← mkCongrArg (← ctxLam fun x => do mkMeet (← mkMeet l p') x) hq
    let back ← law ``BA.meet_meet_split #[l, p', q']
    let prf ← mkEqTrans split (← mkEqTrans r₁ (← mkEqTrans r₂ (← mkEqSymm back)))
    return (← mkMeet p' q', prf)
  | (``BA.or, #[_, _, p, q]) =>
    let (p', hp) ← substLit l a v pos p
    let (q', hq) ← substLit l a v pos q
    let split ← law ``BA.meet_join_distrib #[l, p, q]
    let r₁ ← mkCongrArg (← ctxLam fun x => do mkJoin x (← mkMeet l q)) hp
    let r₂ ← mkCongrArg (← ctxLam fun x => do mkJoin (← mkMeet l p') x) hq
    let back ← law ``BA.meet_join_distrib #[l, p', q']
    let prf ← mkEqTrans split (← mkEqTrans r₁ (← mkEqTrans r₂ (← mkEqSymm back)))
    return (← mkJoin p' q', prf)
  | (``BA.neg, #[_, _, p]) =>
    let (p', hp) ← substLit l a v pos p
    -- `l ⊓ ∼p = l ⊓ ∼(l⊓p) = l ⊓ ∼(l⊓p') = l ⊓ ∼p'`, the `relative_compl` detour
    let outIn ← law ``BA.relative_compl #[l, p]
    let mid ← mkCongrArg (← ctxLam fun x => do mkMeet l (← mkCompl x)) hp
    let backOut ← mkEqSymm (← law ``BA.relative_compl #[l, p'])
    return (← mkCompl p', ← mkEqTrans outIn (← mkEqTrans mid backOut))
  | _ =>
    -- another atom, `⊤` or `⊥`: unchanged
    return (P, ← mkEqRefl (← mkMeet l P))

/-! ### Layer three: the recursion -/

/-- A proof of `P = Q`, or an error naming an assignment on which they differ. `trail`
records the literals chosen so far, for that message. -/
partial def proveEq (atoms : List Expr) (trail : List (Expr × Bool)) (P Q : Expr) :
    BM Expr := do
  match atoms with
  | [] =>
    let (vP, hP) ← evalClosed P
    let (vQ, hQ) ← evalClosed Q
    if vP != vQ then
      let assign ← trail.reverse.mapM fun (a, b) => do
        return m!"{if b then "" else "¬"}{← ppExpr a}"
      throwError "boolean_eq: the two sides are not equivalent; they differ on the \
assignment {MessageData.joinSep assign ", "}"
    mkEqTrans hP (← mkEqSymm hQ)
  | a :: rest =>
    let branch (pos : Bool) : BM Expr := do
      let l ← if pos then pure a else mkCompl a
      let v ← if pos then topE else botE
      let (P', hP) ← substLit l a v pos P
      let (Q', hQ) ← substLit l a v pos Q
      let inner ← proveEq rest ((a, pos) :: trail) P' Q'
      -- `l ⊓ P = l ⊓ P' = l ⊓ Q' = l ⊓ Q`
      let mid ← mkCongrArg (← ctxLam fun x => mkMeet l x) inner
      mkEqTrans hP (← mkEqTrans mid (← mkEqSymm hQ))
    let h₁ ← branch true
    let h₂ ← branch false
    law ``BA.eq_of_meet_eq #[a, P, Q, h₁, h₂]

/-- Prove `lhs = rhs` in the algebra on their type, from the six Boolean Identities. -/
def proveBooleanEq (lhs rhs : Expr) : MetaM Expr := do
  let ty ← inferType lhs
  let inst ← try synthInstance (mkApp (mkConst ``BA) ty) catch _ =>
    throwError "boolean_eq: no Boolean algebra `BA {ty}`; the sides must be propositions or \
relations of some type `v̄ → Prop`"
  (do let lhs ← reify lhs
      let rhs ← reify rhs
      let atoms := (atomsOf rhs (atomsOf lhs #[])).toList
      proveEq atoms [] lhs rhs).run (ty, inst)

/-! ### The front end -/

/-- Prove a Boolean identity from the six Boolean Identities. The goal must be `P = Q` with
`P` and `Q` elements of some `BA τ`, which is to say propositions or relations, built from
atoms by the Boolean operations and the bounds. -/
elab "boolean_eq" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← whnfR (← instantiateMVars (← goal.getType))
    let some (_, lhs, rhs) := ty.eq?
      | throwError "boolean_eq: the goal is not an equation"
    let prf ← proveBooleanEq lhs rhs
    -- The proof is about the canonical formulas, which are definitionally the originals.
    unless ← isDefEq (← inferType prf) ty do
      throwError "boolean_eq: internal error, the proof built does not fit the goal"
    goal.assign prf

/-! ### The propositional case of Appendix A

Appendix A shows every `H` axiom identical to `⊤` and every rule to preserve that, and
then converts `(P ↔ Q) = ⊤` into `P = Q`. The last step is `eq_of_iff_eq_top` below, and
with the tactic it is four lines: conjoin `⊤` to each side, replace it by the biconditional,
and observe that `P ∧ (P ↔ Q)` and `Q ∧ (P ↔ Q)` are tautologically identical.

Together with `boolean_eq`, which settles any tautology, this closes the `PC` case: a
propositional `H`-theorem `P ↔ Q` yields the identity `P = Q` from the six Boolean
Identities. What remains for stage three is the quantifier part, `UI`, `EG`, `Gen` and
`Inst`, from the five Classicist Identities. -/

/-- From `(P ↔ Q) = ⊤` to `P = Q`, where `↔` is the paper's abbreviation. This is the
propositional half of Appendix A's conversion. -/
theorem eq_of_iff_eq_top {p q : Prop} (h : iff p q = Top) : p = q :=
  have key : (p ∧ iff p q) = (q ∧ iff p q) := by boolean_eq
  calc p = (p ∧ Top) := (meet_top p).symm
    _ = (p ∧ iff p q) := by rw [h]
    _ = (q ∧ iff p q) := key
    _ = (q ∧ Top) := by rw [h]
    _ = q := meet_top q

/-- And back: identical propositions have a biconditional identical to `⊤`. So
`(P ↔ Q) = ⊤` and `P = Q` are interchangeable, which is Propositional Equivalence read as
an identity. -/
theorem iff_eq_top_of_eq {p q : Prop} (h : p = q) : iff p q = Top :=
  have key : iff q q = Top := by boolean_eq
  h ▸ key

end Classicism.Strict
