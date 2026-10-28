import Classicism.MathematicalContingency.Certificates.CountableConditions08
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.countableDomain_coext.derivable
#check Classicism.MathematicalContingency.countableDomain_empty.derivable
#check Classicism.MathematicalContingency.countableCondition_coext.derivable
#check Classicism.MathematicalContingency.countableCondition_representative.derivable
#check Classicism.MathematicalContingency.countableCondition_empty.derivable
#check Classicism.MathematicalContingency.countableConditionOrder_partialOrder.derivable
#check Classicism.MathematicalContingency.countableDomain_row.derivable
#check Classicism.MathematicalContingency.countableCondition_row.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.CountableConditions01,`Classicism.MathematicalContingency.Certificates.CountableConditions02,`Classicism.MathematicalContingency.Certificates.CountableConditions03,`Classicism.MathematicalContingency.Certificates.CountableConditions04,`Classicism.MathematicalContingency.Certificates.CountableConditions05,`Classicism.MathematicalContingency.Certificates.CountableConditions06,`Classicism.MathematicalContingency.Certificates.CountableConditions07,`Classicism.MathematicalContingency.Certificates.CountableConditions08] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
