import Diagnostics.DeepSplitCommonBound
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.doubleHartogs_commonPairedBound_nontrivial.derivable
run_cmd do
  let env ← Lean.getEnv
  let some idx := env.getModuleIdx? `Diagnostics.DeepSplitCommonBound
    | throwError "missing imported certificate module"
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
      if let .thmInfo _ := ci then count := count + 1
  Lean.logInfo s!"imported_conversion_auxiliary_theorems={count}"
