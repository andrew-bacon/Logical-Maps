import Classicism.MathematicalContingency.Certificates.RegularOpenCones08
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.roCone_maps.derivable
#check Classicism.MathematicalContingency.roCone_contains.derivable
#check Classicism.MathematicalContingency.roCone_below.derivable
#check Classicism.MathematicalContingency.roEndpoints_extents.derivable
#check Classicism.MathematicalContingency.roNonzero_member.derivable
#check Classicism.MathematicalContingency.regularOpen_denseCones.derivable
#check Classicism.MathematicalContingency.regularOpen_incompatibleCones.derivable
#check Classicism.MathematicalContingency.regularOpen_completion.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.RegularOpenCones01,`Classicism.MathematicalContingency.Certificates.RegularOpenCones02,`Classicism.MathematicalContingency.Certificates.RegularOpenCones03,`Classicism.MathematicalContingency.Certificates.RegularOpenCones04,`Classicism.MathematicalContingency.Certificates.RegularOpenCones05,`Classicism.MathematicalContingency.Certificates.RegularOpenCones06,`Classicism.MathematicalContingency.Certificates.RegularOpenCones07,`Classicism.MathematicalContingency.Certificates.RegularOpenCones08] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
