import Classicism.MathematicalContingency.Certificates.NaturalCHNonnecessity02
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.contingency_not_necessary.derivable
#check Classicism.MathematicalContingency.natural_CH_nonnecessity.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.NaturalCHNonnecessity01,`Classicism.MathematicalContingency.Certificates.NaturalCHNonnecessity02] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
