import Diagnostics.DeepSplitTranslate
import Classicism.MathematicalContingency.Certificates.HartogsDistinctness04
import Classicism.MathematicalContingency.Certificates.HartogsTheorem13
import Classicism.MathematicalContingency.StableHartogsIndex
import Classicism.MathematicalContingency.Certificates.StableHartogsIndex02
/-! OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.Meta.DeepSplitTranslate.conversionTrace "stable-index-03-conversions.trace"
#classicism_deep_split_derive Classicism.MathematicalContingency.stable_hartogs_presentation
#print axioms Classicism.MathematicalContingency.stable_hartogs_presentation.derivable
