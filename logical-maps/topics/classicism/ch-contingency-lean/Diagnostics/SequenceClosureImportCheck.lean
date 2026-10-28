import Classicism.MathematicalContingency.Certificates.CountableSequenceClosure03
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.descending_maps_antitone.derivable
#check Classicism.MathematicalContingency.descending_maps_directed.derivable
#check Classicism.MathematicalContingency.countableDomainCode_graph_coext.derivable
#check Classicism.MathematicalContingency.maps_graph_evaluation_coext.derivable
#check Classicism.MathematicalContingency.countableCondition_countablyClosed_of_codes.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.DescendingSequences01,`Classicism.MathematicalContingency.Certificates.DescendingSequences02,`Classicism.MathematicalContingency.Certificates.CountableSequenceClosure01,`Classicism.MathematicalContingency.Certificates.CountableSequenceClosure02,`Classicism.MathematicalContingency.Certificates.CountableSequenceClosure03] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
