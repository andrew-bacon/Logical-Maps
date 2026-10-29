import Classicism.MathematicalContingency.Certificates.CountableDirectedUnions02
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.countableDomainCode_coext.derivable
#check Classicism.MathematicalContingency.firstDomainStage_exists.derivable
#check Classicism.MathematicalContingency.firstDomainStage_unique.derivable
#check Classicism.MathematicalContingency.countableDomain_indexed_union.derivable
#check Classicism.MathematicalContingency.uniformDomainCodes_of_wellOrder.derivable
#check Classicism.MathematicalContingency.countableDomain_indexed_union_of_wellOrdered_codes.derivable
#check Classicism.MathematicalContingency.ternaryFunctional_directed_union.derivable
#check Classicism.MathematicalContingency.countableCondition_directed_lowerBound.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.CountableDomainFamilies01,`Classicism.MathematicalContingency.Certificates.CountableDomainFamilies02,`Classicism.MathematicalContingency.Certificates.CountableDomainFamilies03,`Classicism.MathematicalContingency.Certificates.CountableDomainFamilies04,`Classicism.MathematicalContingency.Certificates.CountableDomainFamilies05,`Classicism.MathematicalContingency.Certificates.CountableDomainFamilies06,`Classicism.MathematicalContingency.Certificates.CountableDirectedUnions01,`Classicism.MathematicalContingency.Certificates.CountableDirectedUnions02] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
