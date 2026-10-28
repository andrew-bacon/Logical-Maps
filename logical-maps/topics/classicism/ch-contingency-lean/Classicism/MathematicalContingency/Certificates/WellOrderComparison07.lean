import Classicism.MathematicalContingency.WellOrderComparison
import Classicism.MathematicalContingency.Certificates.WellOrderComparison06
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.wellOrder_comparison
#print axioms Classicism.MathematicalContingency.wellOrder_comparison.derivable
