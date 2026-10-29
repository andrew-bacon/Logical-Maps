import Classicism.MathematicalContingency.Certificates.NaturalCohenCoordinates01
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 4
#check Classicism.MathematicalContingency.hartogs_coordinate_bounds.derivable
#check Classicism.MathematicalContingency.natural_hartogs_coordinate_bounds.derivable
#check Classicism.MathematicalContingency.natural_cohen_possible_not_cardinalCH_of_closedSegments.derivable
run_cmd do
  let env ← Lean.getEnv
  for m in #[`Classicism.MathematicalContingency.Certificates.HartogsCoordinates05,
    `Classicism.MathematicalContingency.Certificates.HartogsCoordinates06,
    `Classicism.MathematicalContingency.Certificates.NaturalCohenCoordinates01] do
    let some idx := env.getModuleIdx? m | throwError "missing imported certificate module {m}"
    let mut count := 0
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && (`Classicism.GeneratedConversion).isPrefixOf n then
        if let .thmInfo _ := ci then count := count + 1
    Lean.logInfo s!"{m}: imported_conversion_auxiliary_theorems={count}"
