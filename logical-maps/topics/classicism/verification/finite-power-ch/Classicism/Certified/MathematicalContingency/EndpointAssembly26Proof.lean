import Classicism.Certified.MathematicalContingency.EndpointAssembly25
import Classicism.Results.MathematicalContingency.GenericRegularOpenMP
import Classicism.Tools.DeepSplitTranslate

/-! Close the negative realization proof independently of its statement reflection.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.Meta.DeepSplitTranslate.profile true
set_option Classicism.Meta.DeepSplitTranslate.progress ".lake/finite-power-endpoint-progress.log"
set_option Classicism.Meta.DeepSplitTranslate.conversionTrace ".lake/finite-power-conversion-progress.log"

#classicism_deep_split_derive Classicism.MathematicalContingency.FinitePower.negative_MP_realization_via_generic
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization_via_generic.derivable
