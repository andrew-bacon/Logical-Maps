import Classicism.MathematicalContingency.Certificates.RowRepresentativeMaps03
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.rowRepresentatives_maps.derivable
#check Classicism.MathematicalContingency.rowRepresentatives_necessary_maps.derivable
#check Classicism.MathematicalContingency.rowRepresentatives_surjects.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.RowRepresentativeMaps01,`Classicism.MathematicalContingency.Certificates.RowRepresentativeMaps02,`Classicism.MathematicalContingency.Certificates.RowRepresentativeMaps03] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
