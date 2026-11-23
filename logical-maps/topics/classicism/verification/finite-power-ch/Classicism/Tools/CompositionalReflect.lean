import Classicism.Tools.DeepSplitTranslate
import Classicism.Tools.DenotationSteps

/-! Reflection by small congruence steps. Each nontrivial equality is abstracted
over its free variables and synchronously kernel checked before reuse. This is
metalogical reflection only: it does not supply an object-language derivation.
No whole-formula definitional equality test is used.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.Meta.CompositionalReflect
open Lean Meta Elab Term

structure State where
  declPrefix : Name
  cache : Std.HashMap Expr Name := {}
  count : Nat := 0
  stopAfter : Nat := 0
  onStep : Nat → TermElabM Unit := fun _ => pure ()

private initialize segmentFinished : InternalExceptionId ←
  registerInternalExceptionId `Classicism.Meta.CompositionalReflect.segmentFinished

abbrev M := StateRefT State TermElabM

private def parameters (ty : Expr) : MetaM (Array Expr) := do
  let used ← (Lean.collectFVars {} ty).addDependencies
  return (← getLCtx).getFVarIds.filterMap fun id =>
    if used.fvarSet.contains id then some (mkFVar id) else none

private def save (lhs rhs value : Expr) : M Expr := do
  let rhsTy ← inferType rhs
  let ty := mkApp3 (mkConst ``Eq [← getLevel rhsTy]) rhsTy lhs rhs
  let xs ← parameters ty
  let closedTy ← mkForallFVars xs ty
  if let some n := (← get).cache[closedTy]? then return mkAppN (mkConst n) xs
  let value ← instantiateMVars (← mkLambdaFVars xs value)
  if value.hasMVar || value.hasFVar || value.hasSorry then
    throwError "compositional reflection: unresolved proof"
  let s ← get
  let n := s.declPrefix ++ Name.mkSimple s!"step{s.count}"
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := n, levelParams := [], type := closedTy, value })
  modify fun s => { s with count := s.count + 1, cache := s.cache.insert closedTy n }
  if (s.count + 1) % 100 == 0 then
    -- These are disposable elaborator caches, not checked declarations or
    -- reflection lemmas. The environment and the explicit lemma cache remain.
    Lean.Meta.resetCache
    s.onStep (s.count + 1)
  if s.stopAfter != 0 && s.count + 1 >= s.stopAfter then
    throw <| Exception.internal segmentFinished
  return mkAppN (mkConst n) xs

private def cached? (lhs rhs : Expr) : M (Option Expr) := do
  if (← get).cache.isEmpty then return none
  let rhsTy ← inferType rhs
  let ty := mkApp3 (mkConst ``Eq [← getLevel rhsTy]) rhsTy lhs rhs
  let xs ← parameters ty
  let closedTy ← mkForallFVars xs ty
  return (← get).cache[closedTy]?.map fun n => mkAppN (mkConst n) xs

/-- Unfold exactly one syntax constructor through its generic kernel-checked
equation, without reducing the recursive denotation function on its children. -/
private def denotationStep? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Classicism.Meta.Term.denote && args.size ≥ 6 do return none
  let term ← whnfR args[4]!
  let targs := term.getAppArgs
  let ctor := term.getAppFn.constName!
  unless ctor.getPrefix == ``Classicism.Meta.Term do
    throwError "compositional reflection: expected syntax constructor"
  let lemma := `Classicism.Meta.DenotationSteps ++ Name.mkSimple ctor.getString!
  unless (← getEnv).contains lemma do
    throwError "compositional reflection: missing denotation equation for {ctor}"
  -- Term constructors begin with Sig and Γ. The equations insert I between
  -- those parameters and append the environment after the constructor data.
  let mut proof := mkAppN (mkConst lemma)
    (#[targs[0]!, args[1]!, targs[1]!] ++ targs.extract 2 targs.size ++ #[args[5]!])
  for a in args.extract 6 args.size do proof ← mkCongrFun proof a
  let proofTy ← inferType proof
  let some (_, _, value) := proofTy.eq? | throwError "denotation equation is not an equality"
  return some (value, proof)

/-- Compare paired heads, descending under binders and through applications.
The only non-definitional steps are the native propositional reflection lemmas
and congruence/extensionality used to assemble the equalities. -/
partial def prove (left right : Expr) : M Expr := do
  checkSystem "compositional reflection"
  if left == right then return ← mkEqRefl left
  let head ← whnfR left
  if let some (next, h) ← denotationStep? head then
    -- The generic constructor equation is already checked. Retain it in the
    -- enclosing proof instead of creating another declaration for every small
    -- interpreter reduction. Cache the resulting structural equalities below.
    return ← mkEqTrans h (← prove next right)
  if let some h ← cached? left right then return h
  let lhs ← whnf head
  let rhs ← whnf right
  if lhs == rhs then return ← save left right (← mkEqRefl rhs)
  let value ← go lhs rhs
  save left right value
where
  go (lhs rhs : Expr) : M Expr := do
    -- The syntax uses classical abbreviations for implication, truth, and iff.
    if rhs.isConstOf ``True then
      return mkConst ``Classicism.Meta.top_eq
    if rhs.isConstOf ``False then
      return mkConst ``Classicism.Meta.bot_eq
    if let .forallE _ d b _ := rhs then
      if (← isProp d) && !b.hasLooseBVars then
        if lhs.isAppOfArity ``Or 2 then
          let middle := mkApp2 (mkConst ``Or) (mkApp (mkConst ``Not) d) b
          let h := mkApp2 (mkConst ``Classicism.Meta.imp_eq) d b
          return ← mkEqTrans (← prove lhs middle) h
    if let some (a, b) := rhs.app2? ``Iff then
      -- Expand the small source-side connective. Do not normalize an arbitrary
      -- denotation child merely to recognize the primitive iff abbreviation.
      let ab := mkApp2 (mkConst ``Or) (mkApp (mkConst ``Not) a) b
      let ba := mkApp2 (mkConst ``Or) (mkApp (mkConst ``Not) b) a
      let h := mkApp2 (mkConst ``Classicism.Meta.iff_eq) a b
      return ← mkEqTrans (← prove lhs (mkApp2 (mkConst ``And) ab ba)) h
    match lhs, rhs with
    | .forallE n d b bi, .forallE _ d' b' _ =>
      if (← isProp d) && !b.hasLooseBVars && !b'.hasLooseBVars then
        return ← mkImpCongr (← prove d d') (← prove b b')
      unless ← isDefEq d d' do
        throwError "compositional reflection: different quantifier domains"
      withLocalDecl n bi d fun x => do
        let h ← prove (b.instantiate1 x) (b'.instantiate1 x)
        mkForallCongr (← mkLambdaFVars #[x] h)
    | .lam n d b bi, .lam _ d' b' _ =>
      unless ← isDefEq d d' do
        throwError "compositional reflection: different lambda domains"
      withLocalDecl n bi d fun x => do
        let h ← prove (b.instantiate1 x) (b'.instantiate1 x)
        mkAppM ``funext #[← mkLambdaFVars #[x] h]
    | .lam n d b bi, _ =>
      withLocalDecl n bi d fun x => do
        let h ← prove (b.instantiate1 x) (mkApp rhs x)
        mkAppM ``funext #[← mkLambdaFVars #[x] h]
    | _, .lam n d b bi =>
      withLocalDecl n bi d fun x => do
        let h ← prove (mkApp lhs x) (b.instantiate1 x)
        mkAppM ``funext #[← mkLambdaFVars #[x] h]
    | .app f a, .app g b =>
      let aTy ← whnf (← inferType a)
      if (aTy.isSort && !aTy.isProp) || (← isProp aTy) then
        unless ← isDefEq a b do
          throwError "compositional reflection: type/proof arguments differ"
        return ← mkCongrFun (← prove f g) a
      return ← mkCongr (← prove f g) (← prove a b)
    | _, _ =>
      -- Atomic constants/variables may differ only by reducible type wrappers.
      if lhs.isAtomic && rhs.isAtomic then
        if ← isDefEq lhs rhs then return ← mkEqRefl rhs
      throwError "compositional reflection: unmatched heads\n{lhs.getAppFn}\n{rhs.getAppFn}"

def reflect (declPrefix : Name) (lhs rhs : Expr)
    (onStep : Nat → TermElabM Unit := fun _ => pure ()) : TermElabM Expr := do
  onStep 0
  let (proof, state) ← (prove lhs rhs).run { declPrefix, onStep }
  logInfo m!"compositional reflection: {state.count} checked equality lemmas"
  return proof

/-- Reuse only previously exported, kernel-checked equality lemmas. A bounded
segment may export more lemmas without asserting the final reflection. Only the
specific budget exception is caught; proof errors always fail the compilation. -/
def reflectSegment (declPrefix : Name) (lhs rhs : Expr) (budget : Nat)
    (onStep : Nat → TermElabM Unit := fun _ => pure ()) : TermElabM (Option Expr) := do
  unless budget > 0 do throwError "reflection segment budget must be positive"
  let mut state : State := { declPrefix, onStep }
  for (n, ci) in (← getEnv).constants.toList do
    if n.getPrefix == declPrefix then
      if let .thmInfo info := ci then
        let some k := (n.getString!.drop 4).toString.toNat? | continue
        state := { state with
          cache := state.cache.insert info.type n
          count := max state.count (k + 1) }
  let initial := state.count
  state := { state with stopAfter := initial + budget }
  logInfo m!"reflection segment: reusing {initial} checked equality lemmas"
  try
    let (proof, finalState) ← (prove lhs rhs).run state
    logInfo m!"reflection segment: complete with {finalState.count} checked equality lemmas"
    return some proof
  catch ex =>
    match ex with
    | .internal id _ =>
      if id == segmentFinished then
        logInfo m!"reflection segment: exported through step{initial + budget - 1}; final reflection pending"
        return none
      else throw ex
    | _ => throw ex

end Classicism.Meta.CompositionalReflect
