import Classicism.MathematicalContingency.Certificates.CountableRowCoverage02
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.countable_names_cover_current.derivable
#check Classicism.MathematicalContingency.frozen_rows_cover_preserved_power.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.CountableRowCoverage01,`Classicism.MathematicalContingency.Certificates.CountableRowCoverage02] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
