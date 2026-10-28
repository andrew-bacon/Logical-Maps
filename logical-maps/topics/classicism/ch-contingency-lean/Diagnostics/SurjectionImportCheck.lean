import Classicism.MathematicalContingency.Certificates.WellOrderSurjection04
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.leastPreimage_injects.derivable
#check Classicism.MathematicalContingency.embeds_of_surjects_wellOrder.derivable
#check Classicism.MathematicalContingency.possible_embeds_of_possible_surjects.derivable
#check Classicism.MathematicalContingency.possible_rigidPower_equinumerous_hartogs_of_possible_surjects.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.WellOrderSurjection01,
    `Classicism.MathematicalContingency.Certificates.WellOrderSurjection02,
    `Classicism.MathematicalContingency.Certificates.WellOrderSurjection03,
    `Classicism.MathematicalContingency.Certificates.WellOrderSurjection04] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
