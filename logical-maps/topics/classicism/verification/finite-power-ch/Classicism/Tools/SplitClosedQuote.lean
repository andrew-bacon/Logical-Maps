import Classicism.Tools.SharedClosedQuote

/-! Separately compiled reflection of closed implication components. Components
are proposition definitions, not axioms or assertions of their truth. Assembly
checks literal agreement with the original native quotation and reflection into
the exact original theorem type. OpenAI Codex, prompted by Andrew Bacon,
1 November 2026. -/
namespace Classicism.Meta.SplitClosedQuote
open Lean Meta Elab Term Command

theorem holds_imp {Sig : Signature} (I : Interp Sig) (p q : Sentence Sig) :
    Sentence.holds I (Term.imp p q) = (Sentence.holds I p → Sentence.holds I q) :=
  Classicism.Meta.imp_eq _ _

private def pieces (name : Name) : MetaM (Array Expr) := do
  let info ← getConstInfo name
  let .thmInfo _ := info | throwError "split quote: expected a theorem"
  unless info.levelParams.isEmpty do throwError "split quote: expected a closed theorem"
  let mut rest := info.type
  let mut result := #[]
  repeat
    match rest with
    | .forallE _ d b _ =>
      unless (← isProp d) && !b.hasLooseBVars do break
      result := result.push d
      rest := b
    | _ => break
  return result.push rest

private def pieceName (name : Name) (i : Nat) : Name := name ++ Name.mkSimple s!"piece{i}"

def quotePiece (name : Name) (i : Nat) (quotationOnly : Bool := false) : TermElabM Unit := do
  let ps ← pieces name
  unless i < ps.size do throwError "split quote: component index out of range"
  let n := pieceName name i
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl {
      name := n, levelParams := [], type := mkSort .zero, value := ps[i]!,
      hints := .abbrev, safety := .safe })
  SharedClosedQuote.quoteClosed n quotationOnly
  if quotationOnly then logInfo m!"{n}: component quotation saved; reflection pending"
  else logInfo m!"{n}: component reflects ✓"

def assemble (name : Name) : TermElabM Unit := do
  let ps ← pieces name
  let sig := DeepSplitTranslate.sigE
  let I := mkApp (mkConst ``Classicism.Meta.Interp.ofDomain) (mkConst ``Classicism.e)
  let last := pieceName name (ps.size - 1)
  let mut q := Lean.mkConst (last ++ `quoted)
  let mut proof := Lean.mkConst (last ++ `reflect)
  for i in (List.range (ps.size - 1)).reverse do
    let n := pieceName name i
    let p := Lean.mkConst (n ++ `quoted)
    let h := mkAppN (mkConst ``holds_imp) #[sig, I, p, q]
    proof ← mkEqTrans h (← mkImpCongr (mkConst (n ++ `reflect)) proof)
    q := mkAppN (mkConst ``Classicism.Meta.Term.imp)
      #[sig, mkApp (mkConst ``List.nil [.zero]) (mkConst ``Classicism.Meta.Ty), p, q]
  let sentenceTy := mkApp (mkConst ``Classicism.Meta.Sentence) sig
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl {
      name := name ++ `quoted, levelParams := [], type := sentenceTy, value := q,
      hints := .abbrev, safety := .safe })
  setReducibilityStatus (name ++ `quoted) .reducible
  let original := (← getConstInfo name).type
  let ctx : DeepSplitTranslate.TCtx := {
    ax := mkApp (mkConst ``Classicism.Meta.C.axiomsMinus) sig, axIsC := false }
  let (native, _) ←
    ((DeepSplitTranslate.withCaches (DeepSplitTranslate.quoteF original)).run ctx).run {}
  let quoted := Lean.mkConst (name ++ `quoted)
  let agreementTy := mkApp3 (mkConst ``Eq [.succ .zero]) sentenceTy quoted native
  let agreementVal := mkApp2 (mkConst ``Eq.refl [.succ .zero]) sentenceTy quoted
  let lhs := mkApp3 (mkConst ``Classicism.Meta.Sentence.holds) sig I quoted
  let reflectTy := mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero) lhs original
  if proof.hasMVar || proof.hasFVar || proof.hasSorry then
    throwError "split quote: unresolved assembled reflection"
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {
      name := name ++ `quotation_agreement, levelParams := [],
      type := agreementTy, value := agreementVal })
    addDecl (.thmDecl {
      name := name ++ `reflect, levelParams := [], type := reflectTy, value := proof })
  logInfo m!"{name}: native literal quotation agreement; assembled reflects ✓"

syntax (name := quotePieceCmd) "#classicism_shared_quote_piece " ident num : command
syntax (name := assembleCmd) "#classicism_shared_quote_assemble " ident : command

@[command_elab quotePieceCmd] def elabPiece : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some i := stx[2].isNatLit? | throwError "expected component index"
  liftTermElabM (quotePiece n i)

@[command_elab assembleCmd] def elabAssemble : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  liftTermElabM (assemble n)

syntax (name := quotePieceSyntaxCmd) "#classicism_shared_quote_piece_syntax " ident num : command
@[command_elab quotePieceSyntaxCmd] def elabPieceSyntax : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some i := stx[2].isNatLit? | throwError "expected component index"
  liftTermElabM (quotePiece n i true)

end Classicism.Meta.SplitClosedQuote
