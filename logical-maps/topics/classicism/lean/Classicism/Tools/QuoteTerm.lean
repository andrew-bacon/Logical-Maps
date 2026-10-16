import Classicism.Tools.Quote
import Classicism.Semantics.Denotation

/-!
# Quotation of closed terms

`#classicism_quote_term foo`: the companion of `#classicism_quote` for a closed definition at a
type of the object language rather than a statement. It declares `foo.term`, the quoted term,
and `foo.reflect`, that the term denotes `foo` over the domain `e`, by `rfl`.
-/

open Lean Meta Elab Term Command

namespace Classicism.Meta.Quote

/-- Quote `foo`, a definition at a type of the object language, possibly after leading type
parameters `(σ : Type) [Ty σ]`. Returns the quoted term as a function of one metalogical
type per type parameter, its type, and the reflection statement and its proof: that the
term denotes `foo` over the domain `e`, the parameters read as the denotations of the
metalogical types. -/
def quoteTermDef (n : Name) : TermElabM (Expr × Expr × Expr × Expr) := do
  let info ← getConstInfo n
  forallTelescope info.type fun ys body => do
    -- the leading type parameters and their `Ty` instances; the rest is the type quoted
    let mut k := 0
    for y in ys do
      let t ← whnf (← inferType y)
      if (t.isSort && !t.isProp) || (← isClass? t) == some ``Classicism.Ty then k := k + 1
      else break
    let xs := ys.extract 0 k
    let bodyTy ← mkForallFVars (ys.extract k ys.size) body
    let tys ← xs.filterM fun x => do let t ← whnf (← inferType x); pure (t.isSort && !t.isProp)
    let val := mkAppN (Lean.mkConst n (info.levelParams.map mkLevelParam)) xs
    let rec go (i : Nat) (ctx : QCtx) (tvs : Array Expr) : TermElabM (Expr × Expr × Expr × Expr) := do
      if h : i < tys.size then
        let σ := tys[i]
        withLocalDeclD ((← σ.fvarId!.getUserName).appendAfter "'") (mkConst ``Classicism.Meta.Ty)
          fun tv => go (i + 1) { ctx with tyVars := (σ.fvarId!, .ty, tv) :: ctx.tyVars } (tvs.push tv)
      else
        let σq ← (quoteTy bodyTy).run ctx
        let stx ← (quoteTerm ((← unfoldDefinition? val).getD val)).run ctx
        let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
        let nilCtx := mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``Classicism.Meta.Ty)
        let termTy := mkApp3 (Lean.mkConst ``Classicism.Meta.Term) pureSig nilCtx σq
        let t ← elabTermEnsuringType stx (some termTy)
        synthesizeSyntheticMVarsNoPostponing
        let t ← instantiateMVars t
        if t.hasMVar then throwError "quote: the term has unresolved holes:{indentExpr t}"
        -- the parameters of `foo`, read: a type as the denotation of its metalogical type,
        -- an instance as the marker
        let D : Expr := Lean.mkConst ``Classicism.e
        let mut args : Array Expr := #[]
        let mut ti := 0
        for x in xs do
          let t ← whnf (← inferType x)
          if t.isSort then
            args := args.push (mkApp2 (Lean.mkConst ``Classicism.Meta.Ty.denote) D tvs[ti]!)
            ti := ti + 1
          else
            let some j := tys.idxOf? (t.getAppArgs[0]!)
              | throwError "quote: an instance of {n} not on one of its type parameters"
            args := args.push (mkApp2 (Lean.mkConst ``Classicism.Ty.mk)
              (mkApp2 (Lean.mkConst ``Classicism.Meta.Ty.denote) D tvs[j]!) (Lean.mkConst ``Unit.unit))
        let rhs := mkAppN (Lean.mkConst n (info.levelParams.map mkLevelParam)) args
        let I := mkApp (Lean.mkConst ``Classicism.Meta.Interp.ofDomain) D
        let lhs ← mkAppM ``Classicism.Meta.Term.denote #[I, t, mkApp (Lean.mkConst ``Classicism.Meta.Env.nil) D]
        let eq ← mkEq lhs rhs
        let pf ← if ← isDefEq lhs rhs then mkEqRefl lhs else
          -- `→` is quoted as `¬p ∨ q`: rewrite back, as `#classicism_quote` does
          let defs ← reflectDefs rhs
          let lemmas ← (reflectSimpSet ++ defs).mapM fun n =>
            `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
          let stx ← `(by simp only [$lemmas,*]; try rfl)
          let v ← Term.withoutErrToSorry do
            let v ← elabTermEnsuringType stx (some eq)
            synthesizeSyntheticMVarsNoPostponing
            instantiateMVars v
          if v.hasSorry then throwError "quote: {n} does not reflect"
          pure v
        return (← mkLambdaFVars tvs t, ← mkForallFVars tvs termTy,
          ← mkForallFVars tvs eq, ← mkLambdaFVars tvs pf)
    go 0 {} #[]

/-- `#classicism_quote_term foo`: quote the value of a definition `foo : T` at a type of the
object language, declaring `foo.term : Term Signature.pure [] ⌜T⌝` and `foo.reflect`, that its
denotation over the domain `e` is `foo`, by `rfl`. A definition with leading type parameters
`(σ : Type) [Ty σ]` gets `foo.term : (σ' : Ty) → …`, one metalogical type per parameter, and
`foo.reflect` for every such type, with `foo`'s parameter read as its denotation. -/
elab "#classicism_quote_term " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    liftTermElabM do
      let (t, termTy, eq, pf) ← quoteTermDef n
      let tName := n ++ Name.mkSimple "term"
      let rName := n ++ Name.mkSimple "reflect"
      let dv : DefinitionVal := { name := tName, levelParams := [], type := termTy, value := t, hints := .abbrev, safety := .safe }
      let tv : TheoremVal := { name := rName, levelParams := [], type := eq, value := pf }
      withOptions (Elab.async.set · false) do
        addDecl (.defnDecl dv)
        addDecl (.thmDecl tv)
      enableRealizationsForConst tName
      logInfo m!"{n} ⟶ {tName}, reflects ✓"

end Classicism.Meta.Quote
