import Classicism.Tools.DeepSplitTranslate
import Classicism.Results.MathematicalContingency.HartogsIterationBounds
import Classicism.Certified.MathematicalContingency.HartogsIterationBounds02
/-! New composition certificate; historical pairing is an explicit interface.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_deep_split_derive Classicism.MathematicalContingency.FinitePower.secondHartogs_powerBound
#print axioms Classicism.MathematicalContingency.FinitePower.secondHartogs_powerBound.derivable
