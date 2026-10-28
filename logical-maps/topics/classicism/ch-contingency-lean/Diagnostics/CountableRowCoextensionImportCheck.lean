import Classicism.MathematicalContingency.Certificates.CountableRowCoextension02
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.restricted_pointwise_coext.derivable
#check Classicism.MathematicalContingency.countable_whole_row_coext.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.CountableRowCoextension01,`Classicism.MathematicalContingency.Certificates.CountableRowCoextension02] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
