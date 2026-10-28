import Classicism.MathematicalContingency.Certificates.RegularOpenForcing03
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.countable_regularOpen_completion.derivable
#check Classicism.MathematicalContingency.natural_cohen_regularOpen_completion.derivable
#check Classicism.MathematicalContingency.natural_regularOpen_completions.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.RegularOpenForcing01,`Classicism.MathematicalContingency.Certificates.RegularOpenForcing02,`Classicism.MathematicalContingency.Certificates.RegularOpenForcing03] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
