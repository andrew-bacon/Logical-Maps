import Classicism.MathematicalContingency.Certificates.RegularOpenLattice05
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.roIntersection_fixed.derivable
#check Classicism.MathematicalContingency.roSupremum_exists.derivable
#check Classicism.MathematicalContingency.roInfimum_exists.derivable
#check Classicism.MathematicalContingency.roSupremum_characterization.derivable
#check Classicism.MathematicalContingency.roInfimum_characterization.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.RegularOpenLattice01,`Classicism.MathematicalContingency.Certificates.RegularOpenLattice02,`Classicism.MathematicalContingency.Certificates.RegularOpenLattice03,`Classicism.MathematicalContingency.Certificates.RegularOpenLattice04,`Classicism.MathematicalContingency.Certificates.RegularOpenLattice05] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
