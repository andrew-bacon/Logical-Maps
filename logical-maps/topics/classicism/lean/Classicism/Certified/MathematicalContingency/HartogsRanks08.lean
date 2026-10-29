import Classicism.Results.MathematicalContingency.HartogsRanks
import Classicism.Certified.MathematicalContingency.HartogsRanks07
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.hartogs_strictOrder
#print axioms Classicism.MathematicalContingency.hartogs_strictOrder.derivable
