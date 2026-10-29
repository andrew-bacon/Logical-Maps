import Classicism.Results.MathematicalContingency.HartogsTheorem
import Classicism.Certified.MathematicalContingency.HartogsTheorem03
/-! One theorem per file to bound certificate-generation memory. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.rank_preimage_subset
#print axioms Classicism.MathematicalContingency.rank_preimage_subset.derivable
