import Classicism.MathematicalContingency.Certificates.StableHartogsIndex04
import Classicism.MathematicalContingency.Certificates.PositiveOrderTypeCHBridge03
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.stable_hartogs_presentation.derivable
#check Classicism.MathematicalContingency.natural_stable_hartogs_presentation.derivable
#check Classicism.MathematicalContingency.equinumerous_of_embeds_countable_segments.derivable
#check Classicism.MathematicalContingency.rigidPower_equinumerous_hartogs_of_embeds.derivable
#check Classicism.MathematicalContingency.possible_rigidPower_equinumerous_hartogs_of_possible_embeds.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.StableHartogsIndex03,
    `Classicism.MathematicalContingency.Certificates.StableHartogsIndex04,
    `Classicism.MathematicalContingency.Certificates.PositiveOrderTypeCHBridge01,
    `Classicism.MathematicalContingency.Certificates.PositiveOrderTypeCHBridge02,
    `Classicism.MathematicalContingency.Certificates.PositiveOrderTypeCHBridge03] do
    let some idx := env.getModuleIdx? m | throwError "missing imported certificate module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
