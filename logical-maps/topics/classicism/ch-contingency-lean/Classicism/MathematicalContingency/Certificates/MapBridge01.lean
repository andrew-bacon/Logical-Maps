import Diagnostics.DeepSplitTranslate
import Classicism.MathematicalContingency.MapBridge
import Classicism.MathematicalContingency.Certificates.ClosedBoundsCH01

/-!
Object-language derivation certificate for the precise three-premise
conditional cardinal CH theorem on the Logical-Maps arrow. This uses the
checkpoint's translator, not the separate map project's verifier.
-/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.Meta.DeepSplitTranslate.conversionTrace "MapBridge01-conversions.trace"

#classicism_deep_split_derive Classicism.MathematicalContingency.bounded_forcing_implies_cardinal_ch_contingency
#print axioms Classicism.MathematicalContingency.bounded_forcing_implies_cardinal_ch_contingency.derivable
