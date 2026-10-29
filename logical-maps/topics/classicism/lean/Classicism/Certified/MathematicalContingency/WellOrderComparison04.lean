import Classicism.Results.MathematicalContingency.WellOrderComparison
import Classicism.Certified.MathematicalContingency.WellOrderComparison03
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.initial_full_range
#print axioms Classicism.MathematicalContingency.initial_full_range.derivable
