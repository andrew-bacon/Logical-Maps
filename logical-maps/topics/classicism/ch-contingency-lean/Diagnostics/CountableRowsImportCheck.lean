import Classicism.MathematicalContingency.Certificates.CountableRows03
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.countableDomain_union.derivable
#check Classicism.MathematicalContingency.countableCondition_union.derivable
#check Classicism.MathematicalContingency.countableCondition_add_row.derivable
#check Classicism.MathematicalContingency.natural_countableCondition_add_row.derivable
#check Classicism.MathematicalContingency.countableDomain_rows_embed.derivable
#check Classicism.MathematicalContingency.countableDomain_unused_row.derivable
#check Classicism.MathematicalContingency.natural_countableCondition_covers_row.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.CountableConditionUnions01,`Classicism.MathematicalContingency.Certificates.CountableConditionUnions02,`Classicism.MathematicalContingency.Certificates.CountableConditionUnions03,`Classicism.MathematicalContingency.Certificates.CountableConditionUnions04,`Classicism.MathematicalContingency.Certificates.CountableRows01,`Classicism.MathematicalContingency.Certificates.CountableRows02,`Classicism.MathematicalContingency.Certificates.CountableRows03] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
