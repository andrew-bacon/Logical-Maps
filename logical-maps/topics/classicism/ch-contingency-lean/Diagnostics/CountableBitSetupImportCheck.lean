import Classicism.MathematicalContingency.Certificates.CountableBitSetup04
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.countableBitSetup_of_common_bound.derivable
#check Classicism.MathematicalContingency.stable_natural_countableBitSetup.derivable
#check Classicism.MathematicalContingency.stable_hartogs_countableBitSetup.derivable
#check Classicism.MathematicalContingency.stable_hartogs_countableBitSetup_of_closedSegments.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.CountableBitSetup01,`Classicism.MathematicalContingency.Certificates.CountableBitSetup02,`Classicism.MathematicalContingency.Certificates.CountableBitSetup03,`Classicism.MathematicalContingency.Certificates.CountableBitSetup04] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
