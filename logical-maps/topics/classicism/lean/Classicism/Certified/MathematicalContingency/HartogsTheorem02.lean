import Classicism.Results.MathematicalContingency.HartogsTheorem
import Classicism.Certified.MathematicalContingency.HartogsTheorem01
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.strictOrder_restrict
#print axioms Classicism.MathematicalContingency.strictOrder_restrict.derivable
