import Classicism.Results.MathematicalContingency.WellOrderTrichotomy
import Classicism.Certified.MathematicalContingency.WellOrderTrichotomy02
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.wellOrder_trichotomy
#print axioms Classicism.MathematicalContingency.wellOrder_trichotomy.derivable
