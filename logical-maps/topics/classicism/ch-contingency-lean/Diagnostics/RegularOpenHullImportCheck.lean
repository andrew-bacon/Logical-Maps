import Classicism.MathematicalContingency.Certificates.RegularOpenHull08
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.roHull_mono.derivable
#check Classicism.MathematicalContingency.roHull_down.derivable
#check Classicism.MathematicalContingency.roHull_extensive.derivable
#check Classicism.MathematicalContingency.roHull_idempotent.derivable
#check Classicism.MathematicalContingency.roFixed_coext.derivable
#check Classicism.MathematicalContingency.roFixed_down.derivable
#check Classicism.MathematicalContingency.roHull_representative.derivable
#check Classicism.MathematicalContingency.roOrder_partialOrder.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.RegularOpenHull01,`Classicism.MathematicalContingency.Certificates.RegularOpenHull02,`Classicism.MathematicalContingency.Certificates.RegularOpenHull03,`Classicism.MathematicalContingency.Certificates.RegularOpenHull04,`Classicism.MathematicalContingency.Certificates.RegularOpenHull05,`Classicism.MathematicalContingency.Certificates.RegularOpenHull06,`Classicism.MathematicalContingency.Certificates.RegularOpenHull07,`Classicism.MathematicalContingency.Certificates.RegularOpenHull08] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
