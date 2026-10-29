import Classicism.Results.MathematicalContingency.HartogsTheorem
import Classicism.Certified.MathematicalContingency.HartogsTheorem14
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.necessary_inductive_hartogs
#print axioms Classicism.MathematicalContingency.necessary_inductive_hartogs.derivable
