import Classicism.Tools.DeepSplitTranslate
import Classicism.Results.MathematicalContingency.PairedRelationCoding
import Classicism.Certified.MathematicalContingency.PairedRelationCoding01
import Classicism.Certified.MathematicalContingency.OrdinalExistenceSupport01
/-! Finite-Power CH Strategy. OpenAI Codex, prompted by Andrew Bacon. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_deep_split_derive Classicism.MathematicalContingency.reflexiveOrderGraph_iso
#print axioms Classicism.MathematicalContingency.reflexiveOrderGraph_iso.derivable
