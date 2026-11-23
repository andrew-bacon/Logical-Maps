import Classicism.Tools.CompositionalReflect

/-! Direct native quotation and compositional reflection for schemas whose
metalogical parameters are ordinary `Ty` parameters. Type parameters remain
external to object quantification. RelTy/Rel/Order/Pointwise parameters are
rejected explicitly; use the general native quoter for those schemas.
This constructs reflection proofs only, never an object derivation.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
open Lean Meta Elab Term
namespace Classicism.Meta.GenericCompositionalQuote

def quoteStatement (name declPrefix : Name)
    (phase : String → TermElabM Unit := fun _ => pure ()) : TermElabM (Expr × Expr × Expr) := do
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
    let rec go (i : Nat) (qctx : Quote.QCtx) (tvs : Array Expr) : TermElabM (Expr × Expr × Expr) := do
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
        let proof ← CompositionalReflect.reflect declPrefix lhs rhs
          (fun n => phase s!"{n} reflection equalities checked")
        let eq := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (mkSort .zero) lhs rhs
        pure (← mkLambdaFVars tvs quoted, ← mkForallFVars tvs eq, ← mkLambdaFVars tvs proof)
    go 0 {} #[]

end Classicism.Meta.GenericCompositionalQuote
