import Classicism.Results.MathematicalContingency.OrdinalUniqueness
import Classicism.Certified.MathematicalContingency.OrdinalUniqueness04
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.separation_of_bounds
#print axioms Classicism.MathematicalContingency.separation_of_bounds.derivable
