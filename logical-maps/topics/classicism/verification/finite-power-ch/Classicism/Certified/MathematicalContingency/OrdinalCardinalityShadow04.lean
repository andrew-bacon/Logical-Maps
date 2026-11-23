import Classicism.Tools.DeepSplitTranslate
import Classicism.Results.MathematicalContingency.OrdinalCardinalityShadow
import Classicism.Certified.MathematicalContingency.OrdinalCardinalityShadow03
/-! Finite-Power CH Strategy. OpenAI Codex, prompted by Andrew Bacon. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_deep_split_derive Classicism.MathematicalContingency.ordinalCard_suc
#print axioms Classicism.MathematicalContingency.ordinalCard_suc.derivable
