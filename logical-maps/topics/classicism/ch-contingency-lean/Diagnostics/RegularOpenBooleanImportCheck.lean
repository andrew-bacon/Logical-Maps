import Classicism.MathematicalContingency.Certificates.RegularOpenBoolean09
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.roMeet_iff.derivable
#check Classicism.MathematicalContingency.roJoin_iff.derivable
#check Classicism.MathematicalContingency.roMeet_of_coext.derivable
#check Classicism.MathematicalContingency.roJoin_of_coext.derivable
#check Classicism.MathematicalContingency.roNeg_fixed.derivable
#check Classicism.MathematicalContingency.roEndpoints_exist.derivable
#check Classicism.MathematicalContingency.roComplement_exists.derivable
#check Classicism.MathematicalContingency.roDistributive.derivable
#check Classicism.MathematicalContingency.regularOpen_cba.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean01,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean02,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean03,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean04,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean05,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean06,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean07,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean08,`Classicism.MathematicalContingency.Certificates.RegularOpenBoolean09] do
    let some idx := env.getModuleIdx? m | throwError "missing module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
