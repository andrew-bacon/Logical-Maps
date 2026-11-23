import Lean

/-! Bounded export of kernel-checked conversion auxiliaries.
The cache is untrusted bookkeeping: an existing theorem is reused only after
its type and axiom footprint are checked. Hash collisions are rejected.
No final derivation is asserted when the auxiliary budget is exhausted.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
open Lean Meta Elab Term

register_option Classicism.Meta.ConversionCache.prefix : String := {
  defValue := ""
  descr := "Nonempty prefix enables reusable conversion auxiliary exports."
}
register_option Classicism.Meta.ConversionCache.budget : Nat := {
  defValue := 0
  descr := "Maximum new conversion auxiliaries in this segment; zero exports none."
}
register_option Classicism.Meta.ConversionCache.progress : String := {
  defValue := ""
  descr := "Optional trace of closure, cache reuse, kernel checks, and budget boundaries."
}
namespace Classicism.Meta.ConversionCache
initialize exported : IO.Ref Nat ← IO.mkRef 0
initialize reused : IO.Ref Nat ← IO.mkRef 0
initialize budgetExceeded : InternalExceptionId ←
  registerInternalExceptionId `Classicism.Meta.ConversionCache.budgetExceeded

private def phase (label : String) : CoreM Unit := do
  let path := Classicism.Meta.ConversionCache.progress.get (← getOptions)
  if path.isEmpty then return
  IO.FS.withFile path .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} {label}; exported={← exported.get}; reused={← reused.get}"

def requirePure (name : Name) : CoreM Unit := do
  for ax in (← collectAxioms name) do
    unless ax == ``propext || ax == ``Quot.sound do
      throwError "conversion cache: unexpected axiom {ax} in {name}"

/-- Close, check, and cache a proof. No declarations bypass the kernel. -/
private def checkedAuxiliaryCore (type value : Expr) : TermElabM Expr := do
  let cachePrefix := Classicism.Meta.ConversionCache.prefix.get (← getOptions)
  if cachePrefix.isEmpty then throwError "conversion cache: no prefix"
  phase "closure-BEGIN"
  let closed ← Closure.mkValueTypeClosure type value true
  unless closed.levelParams.isEmpty do
    throwError "conversion cache: universe-polymorphic closures are unsupported"
  let name := Name.num (cachePrefix.toName ++ `conversionCache) (hash closed.type).toNat
  phase s!"closure-END:{name}"
  if let some info := (← getEnv).find? name then
    let .thmInfo info := info
      | throwError "conversion cache: cached declaration is not a theorem: {name}"
    phase s!"reuse-BEGIN:{name}"
    unless info.levelParams.isEmpty && (← isDefEq info.type closed.type) do
      throwError "conversion cache: type mismatch or hash collision: {name}"
    requirePure name
    reused.modify (· + 1)
    phase s!"reuse-END:{name}"
    return mkAppN (mkConst name) closed.exprArgs
  let count ← exported.get
  if count >= Classicism.Meta.ConversionCache.budget.get (← getOptions) then
    throw <| Exception.internal budgetExceeded
  phase s!"kernel-BEGIN:{name}"
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name, levelParams := [], type := closed.type, value := closed.value })
  phase s!"kernel-END:{name}"
  requirePure name
  exported.modify (· + 1)
  phase s!"audit-END:{name}"
  return mkAppN (mkConst name) closed.exprArgs

/-- Kernel or audit errors must not leave a staged declaration behind. -/
def checkedAuxiliary (type value : Expr) : TermElabM Expr := do
  let before ← getEnv
  let countBefore ← exported.get
  let result ← try
      checkedAuxiliaryCore type value
    catch ex =>
      setEnv before
      throw ex
  -- Stop immediately after the last allowed checked export, before constructing
  -- another conversion. This boundary is outside the error-rollback scope:
  -- the kernel-checked and axiom-audited declaration must survive the pause.
  -- Reusing an existing helper consumes no new-export budget.
  let countAfter ← exported.get
  if countAfter > countBefore &&
      countAfter >= Classicism.Meta.ConversionCache.budget.get (← getOptions) then
    phase "budget-boundary:checked-export-retained"
    throw <| Exception.internal budgetExceeded
  return result

end Classicism.Meta.ConversionCache
