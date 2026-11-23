import Classicism.Certified.MathematicalContingency.EndpointSupport003
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
#classicism_deep_split_derive Classicism.MathematicalContingency.pairMaxAt_exists
#print axioms Classicism.MathematicalContingency.pairMaxAt_exists.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.lexTriple_irrefl
#print axioms Classicism.MathematicalContingency.lexTriple_irrefl.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.pairMaxAt_member
#print axioms Classicism.MathematicalContingency.pairMaxAt_member.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.orderLe_antisymm
#print axioms Classicism.MathematicalContingency.orderLe_antisymm.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.pairMaxAt_unique
#print axioms Classicism.MathematicalContingency.pairMaxAt_unique.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.maxPairOrder_at
#print axioms Classicism.MathematicalContingency.maxPairOrder_at.derivable
