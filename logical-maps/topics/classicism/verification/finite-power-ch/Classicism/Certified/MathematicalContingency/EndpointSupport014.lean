import Classicism.Certified.MathematicalContingency.EndpointAssembly07
import Classicism.Results.MathematicalContingency.FinitePowerCH
import Classicism.Tools.DeepSplitTranslate

/-! Closed derivations needed by the Finite-Power CH endpoint.
Only missing derivations in its proof dependency closure are generated here.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.Meta.DeepSplitTranslate.profile true
set_option Classicism.Meta.DeepSplitTranslate.progress ".lake/finite-power-endpoint-progress.log"
#classicism_derive Classicism.MathematicalContingency.conditionBit_distinct
#print axioms Classicism.MathematicalContingency.conditionBit_distinct.derivable
#classicism_derive Classicism.MathematicalContingency.conditionBit_embeds_two
#print axioms Classicism.MathematicalContingency.conditionBit_embeds_two.derivable
#classicism_derive Classicism.MathematicalContingency.commonPairedBound_of_pairing
#print axioms Classicism.MathematicalContingency.commonPairedBound_of_pairing.derivable
