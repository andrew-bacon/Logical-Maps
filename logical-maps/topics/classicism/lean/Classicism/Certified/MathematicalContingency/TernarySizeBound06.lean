import Classicism.Results.MathematicalContingency.TernarySizeBound
import Classicism.Certified.MathematicalContingency.TernarySizeBound05
/-! OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2000
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.ternaryBound_induction
#print axioms Classicism.MathematicalContingency.ternaryBound_induction.derivable
