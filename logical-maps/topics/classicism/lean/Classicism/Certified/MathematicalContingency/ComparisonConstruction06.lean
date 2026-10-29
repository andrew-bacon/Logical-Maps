import Classicism.Results.MathematicalContingency.ComparisonConstruction
import Classicism.Certified.MathematicalContingency.ComparisonConstruction05
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.comparison_increasing
#print axioms Classicism.MathematicalContingency.comparison_increasing.derivable
