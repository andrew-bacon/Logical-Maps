import Classicism.Tools.DeepSplitTranslate
import Classicism.Results.MathematicalContingency.ChoiceBooleanDecisions
import Classicism.Certified.MathematicalContingency.CountableChoiceFusion02
/-! New dense-decision fusion; historical CBA certificates are reused separately.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_deep_split_derive Classicism.MathematicalContingency.FinitePower.binaryDecisions_of_dense_steps
#print axioms Classicism.MathematicalContingency.FinitePower.binaryDecisions_of_dense_steps.derivable
