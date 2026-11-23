import Classicism.Tools.DeepSplitTranslate
import Classicism.Tools.ConversionCache

/-! Resumable proof translation using bounded checked conversion exports.
Only the ordinary translator may construct the final object derivation.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
open Lean Meta Elab Term Command
namespace Classicism.Meta.StagedDeepSplit

syntax (name := stagedDerive) "#classicism_staged_derive " ident num : command
@[command_elab stagedDerive] def elabStagedDerive : CommandElab := fun stx => do
  let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some budget := stx[2].isNatLit? | throwError "expected conversion budget"
  let before ← getEnv
  ConversionCache.exported.set 0
  ConversionCache.reused.set 0
  try
    unless (← getEnv).contains (name ++ `derivable) do
      withScope (fun scope => { scope with opts := (ConversionCache.prefix.set
          (ConversionCache.budget.set scope.opts budget) name.toString) }) do
        liftTermElabM (DeepSplitTranslate.derive name)
    liftCoreM (ConversionCache.requirePure (name ++ `derivable))
    logInfo m!"staged derivation complete: {name}; new auxiliaries {← ConversionCache.exported.get}; reused {← ConversionCache.reused.get}"
  catch ex =>
    match ex with
    | .internal id _ =>
      if id == ConversionCache.budgetExceeded then
        if (← getEnv).contains (name ++ `derivable) then
          setEnv before
          throwError "staged derivation: final declaration appeared during an incomplete segment"
        logInfo m!"staged derivation incomplete: {name}; new auxiliaries {← ConversionCache.exported.get}; reused {← ConversionCache.reused.get}"
      else
        setEnv before
        throw ex
    | _ =>
      setEnv before
      throw ex

end Classicism.Meta.StagedDeepSplit
