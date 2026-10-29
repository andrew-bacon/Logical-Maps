import Classicism.Results.MathematicalContingency.HartogsRanks
import Classicism.Certified.MathematicalContingency.HartogsRanks05
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.hartogs_lt_trans
#print axioms Classicism.MathematicalContingency.hartogs_lt_trans.derivable
