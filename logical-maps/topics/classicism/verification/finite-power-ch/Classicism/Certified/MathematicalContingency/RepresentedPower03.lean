import Classicism.Tools.DeepSplitTranslate
import Classicism.Results.MathematicalContingency.RepresentedPower
import Classicism.Certified.MathematicalContingency.RepresentedPower02
/-! Finite-Power CH Strategy: one kernel-checked object derivation per target.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_deep_split_derive Classicism.MathematicalContingency.FinitePower.representsPower_pullback
#print axioms Classicism.MathematicalContingency.FinitePower.representsPower_pullback.derivable
