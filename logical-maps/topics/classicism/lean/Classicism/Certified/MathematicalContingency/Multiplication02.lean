import Classicism.Results.MathematicalContingency.Multiplication
import Classicism.Certified.MathematicalContingency.Multiplication01
/-! One theorem per module to bound certificate memory.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.lowerSum_left_comm
#print axioms Classicism.MathematicalContingency.lowerSum_left_comm.derivable
