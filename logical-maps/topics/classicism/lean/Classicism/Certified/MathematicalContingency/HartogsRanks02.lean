import Classicism.Results.MathematicalContingency.HartogsRanks
import Classicism.Certified.MathematicalContingency.HartogsRanks01
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.ordinal_exact_segment
#print axioms Classicism.MathematicalContingency.ordinal_exact_segment.derivable
