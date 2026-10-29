import Lean
import Classicism.Core

/-!
# The paper's symbols

Notation for the pointwise operations at every relational type, so that statements read as
the paper writes them: `X ∧ Y`, `X ∨ Y`, `¬X`, `⊤`, `⊥` for `Rel.and`, `Rel.or`, `Rel.neg`,
`Rel.top`, `Rel.bot`, `X ≤ Y` for the algebraic order `Rel.le`, and `X ≡ Y` for
coextension `∀x̄. X[x̄] ↔ Y[x̄]`. (`X ⊆ Y` for the
inclusion `incl` is in `Core.lean`, always on.) Everything here is elaboration only: the
terms are the same `Rel` operations as before, so the checker, the quoter and the
translator see exactly what they see without it.

The symbols are the paper's, which subscripts them by type and reads `∧_t` as ordinary
conjunction. Lean's `∧`, `∨` and `¬` are `And`, `Or` and `Not`, and at `Prop` both readings
would type-check, so a plain overload would make every propositional formula ambiguous.
Instead the scope `Classicism.Paper` replaces the three parsers with elaborators that decide
**by type**: at `Prop` they produce `And`, `Or` and `Not`, exactly as core Lean does, and at
any other relational type the `Rel` operation. The type is taken from the expected type
when it is known, else from the first operand whose type is known; when neither is known
the elaboration is postponed, as usual. `⊤` and `⊥` are `True` and `False` at `Prop`. So a
file that says `open Paper` loses nothing at `Prop` and gains the paper's spelling at
every other type; goals print the same way.

This file imports `Lean`, for the elaborators, which `Core.lean` does not; a file that
wants the symbols imports it. Files that open the strict algebra (`Strict/Algebra.lean`)
or import Mathlib should not open the scope, since those have `⊤` and `⊥` of their own.
-/

namespace Classicism.Paper
open Lean Elab Term Meta

/-! ### Syntax, at core's precedences, taking priority over core's parsers while the scope
is open -/

scoped syntax:35 (name := pand) (priority := high) term:36 " ∧ " term:35 : term
scoped syntax:30 (name := por) (priority := high) term:31 " ∨ " term:30 : term
scoped syntax:max (name := pnot) (priority := high) "¬" term:40 : term
scoped syntax (name := ptop) (priority := high) "⊤" : term
scoped syntax (name := pbot) (priority := high) "⊥" : term

/-- `∀x̄. X[x̄] ↔ Y[x̄]`, coextension. Not the paper's symbol; it has none. -/
scoped infix:50 " ≡ " => Rel.coext

/-- `X ≤ Y`, the algebraic order `Rel.le` at every relational type, `Prop` included. Outside
the scope `≤` at `Prop` is `entails` (`Core.lean`), the same relation by definition
(`q = (p ∨ q)`) but a different constant; inside it `≤` is always `Rel.le`, the constant
the principles and the records are stated with. -/
scoped syntax:50 (name := ple) (priority := high) term:51 " ≤ " term:51 : term

/-! ### The elaborators -/

/-- Is this type `Prop`? `none` while it is still a metavariable. A sort whose level is not
yet known (`Sort ?u`, the expected type of a type position such as `have h : A ∧ B` or a
theorem's statement) counts as `Prop`: what stands there is a proposition, so the
connective is the logical one. -/
private def isPropType? (t : Expr) : TermElabM (Option Bool) := do
  let t ← whnfR (← instantiateMVars t)
  if t.getAppFn.isMVar then return none
  if t.isSort then return some true
  return some t.isProp

/-- Build the connective once the type is decided: `logical` at `Prop`, else `rel`. The
operands are given as syntax so that the application elaborator handles the `Rel`
instance, which may still involve metavariables. -/
private def build (logical rel : Name) (isProp : Bool) (args : Array Term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let f := mkIdent (if isProp then logical else rel)
  elabTerm (← `($f $args*)) expectedType?

/-- A pointwise connective: decide the type from the expected type, else from the first
operand whose type is known, else postpone. -/
private def elabPointwise (logical rel : Name) (args : Array Term) (expectedType? : Option Expr) :
    TermElabM Expr := do
  if let some ex := expectedType? then
    if let some isProp ← isPropType? ex then
      return ← build logical rel isProp args expectedType?
  for a in args do
    let e ← elabTerm a none
    if let some isProp ← isPropType? (← inferType e) then
      let a' ← exprToSyntax e
      let args := args.map fun b => if b == a then a' else b
      return ← build logical rel isProp args expectedType?
  tryPostpone
  throwError "cannot tell whether this connective is at `Prop` or at a relational type; \
give the type of an operand or of the whole"

@[scoped term_elab pand] def elabAnd : TermElab := fun stx expectedType? =>
  match stx with
  | `($a ∧ $b) => elabPointwise ``And ``Rel.and #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[scoped term_elab por] def elabOr : TermElab := fun stx expectedType? =>
  match stx with
  | `($a ∨ $b) => elabPointwise ``Or ``Rel.or #[a, b] expectedType?
  | _ => throwUnsupportedSyntax

@[scoped term_elab ple] def elabLe : TermElab := fun stx expectedType? =>
  match stx with
  | `($a ≤ $b) => do elabTerm (← `(Rel.le $a $b)) expectedType?
  | _ => throwUnsupportedSyntax

@[scoped term_elab pnot] def elabNot : TermElab := fun stx expectedType? =>
  match stx with
  | `(¬ $a) => elabPointwise ``Not ``Rel.neg #[a] expectedType?
  | _ => throwUnsupportedSyntax

/-- `⊤` and `⊥`: `True` and `False` at `Prop`, else `Rel.top _` and `Rel.bot _`, by the
expected type; postponed until it is known. -/
private def elabConst (logical rel : Name) (expectedType? : Option Expr) : TermElabM Expr := do
  if let some ex := expectedType? then
    if let some isProp ← isPropType? ex then
      if isProp then return mkConst logical
      return ← elabTerm (← `($(mkIdent rel) _)) expectedType?
  tryPostpone
  elabTerm (← `($(mkIdent rel) _)) expectedType?

@[scoped term_elab ptop] def elabTop : TermElab := fun _ expectedType? =>
  elabConst ``True ``Rel.top expectedType?
@[scoped term_elab pbot] def elabBot : TermElab := fun _ expectedType? =>
  elabConst ``False ``Rel.bot expectedType?

/-! ### Printing back -/

@[scoped app_unexpander Rel.and] def unexpandAnd : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ∧ $b)
  | _ => throw ()
@[scoped app_unexpander Rel.or] def unexpandOr : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ∨ $b)
  | _ => throw ()
@[scoped app_unexpander Rel.neg] def unexpandNeg : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `(¬ $a)
  | _ => throw ()
@[scoped app_unexpander Rel.le] def unexpandLe : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ≤ $b)
  | _ => throw ()
@[scoped app_unexpander Rel.top] def unexpandTop : Lean.PrettyPrinter.Unexpander
  | `($_ $_) => `(⊤)
  | _ => throw ()
@[scoped app_unexpander Rel.bot] def unexpandBot : Lean.PrettyPrinter.Unexpander
  | `($_ $_) => `(⊥)
  | _ => throw ()

end Classicism.Paper
