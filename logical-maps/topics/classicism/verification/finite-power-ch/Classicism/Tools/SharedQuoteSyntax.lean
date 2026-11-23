import Classicism.Tools.DeepSplitTranslate

/-! Name closed syntax subtrees before reflection, preserving the exact native
quotation by a separate kernel-checked literal equality. No new syntax or
interpretation is introduced. OpenAI Codex, prompted by Andrew Bacon,
1 November 2026. -/
namespace Classicism.Meta.SharedQuoteSyntax
open Lean Meta Elab Term

structure State where
  declPrefix : Name
  cache : Std.HashMap Expr Expr := {}
  count : Nat := 0

partial def share (original : Expr) : StateRefT State TermElabM Expr := do
  if let some found := (← get).cache[original]? then return found
  let term ← whnfR original
  let head := term.getAppFn
  let mut args := term.getAppArgs
  if head.isConstOf ``Classicism.Meta.Term.app then
    args := args.set! 4 (← share args[4]!)
    args := args.set! 5 (← share args[5]!)
  else if head.isConstOf ``Classicism.Meta.Term.lam then
    args := args.set! 4 (← share args[4]!)
  else
    return original
  let value := mkAppN head args
  let ty ← inferType original
  if value.hasMVar || value.hasFVar || value.hasSorry then
    throwError "shared syntax: expected a closed native syntax expression"
  let s ← get
  let name := s.declPrefix ++ Name.mkSimple s!"part{s.count}"
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl {
      name := name, levelParams := [], type := ty,
      value := value, hints := .abbrev, safety := .safe })
  setReducibilityStatus name .reducible
  let result := Lean.mkConst name
  modify fun s => { s with count := s.count + 1, cache := s.cache.insert original result }
  return result

def compact (declPrefix : Name) (term : Expr)
    (onCount : Nat → TermElabM Unit := fun _ => pure ()) : TermElabM Expr := do
  let (result, state) ← (share term).run { declPrefix }
  onCount state.count
  logInfo m!"shared native syntax: {state.count} checked subtree definitions"
  return result

end Classicism.Meta.SharedQuoteSyntax
