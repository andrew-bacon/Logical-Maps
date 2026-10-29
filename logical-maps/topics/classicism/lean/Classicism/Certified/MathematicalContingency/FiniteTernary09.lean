import Classicism.Results.MathematicalContingency.FiniteTernary
import Classicism.Certified.MathematicalContingency.FiniteTernary08
/-! One theorem per module to bound certificate memory.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.finiteTernary_subset
#print axioms Classicism.MathematicalContingency.finiteTernary_subset.derivable
