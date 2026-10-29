import Classicism.MathematicalContingency.Certificates.MapBridge01

/-! Import the object-language certificate, and check its allowed axioms. -/

#check Classicism.MathematicalContingency.bounded_forcing_implies_cardinal_ch_contingency.derivable

run_cmd do
  let decl := `Classicism.MathematicalContingency.bounded_forcing_implies_cardinal_ch_contingency.derivable
  let axioms ← Lean.collectAxioms decl
  let allowed := [`propext, `Quot.sound]
  unless axioms.all allowed.contains do
    throwError "CH bridge uses unexpected axioms: {axioms}"
  Lean.logInfo m!"CH object-language bridge certificate imported; axioms = {axioms}"
