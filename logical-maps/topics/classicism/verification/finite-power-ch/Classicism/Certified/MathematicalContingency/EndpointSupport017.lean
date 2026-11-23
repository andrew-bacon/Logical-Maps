import Classicism.Certified.MathematicalContingency.EndpointSupport016
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
#classicism_deep_split_derive Classicism.MathematicalContingency.roHull_idempotent
#print axioms Classicism.MathematicalContingency.roHull_idempotent.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.roHull_representative
#print axioms Classicism.MathematicalContingency.roHull_representative.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.roSupremum_exists
#print axioms Classicism.MathematicalContingency.roSupremum_exists.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.roFixed_down
#print axioms Classicism.MathematicalContingency.roFixed_down.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.roIntersection_fixed
#print axioms Classicism.MathematicalContingency.roIntersection_fixed.derivable
#classicism_deep_split_derive Classicism.MathematicalContingency.roInfimum_exists
#print axioms Classicism.MathematicalContingency.roInfimum_exists.derivable
