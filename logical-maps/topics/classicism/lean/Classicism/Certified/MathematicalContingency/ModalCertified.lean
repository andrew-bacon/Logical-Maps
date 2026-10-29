import Classicism.Results.MathematicalContingency.ModalLemmas
import Classicism.Tools.Translate

/-! Object-language derivation certificates for the reusable modal lemmas.
OpenAI Codex, prompted by Andrew Bacon, 24 October 2026. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

#classicism_derive Classicism.MathematicalContingency.rigid_representatives
#classicism_derive Classicism.MathematicalContingency.restricted_barcan
#classicism_derive Classicism.MathematicalContingency.restricted_barcan_dual
#classicism_derive Classicism.MathematicalContingency.local_selection
#classicism_derive Classicism.MathematicalContingency.local_selection_binary
#classicism_derive Classicism.MathematicalContingency.restricted_name_representation

-- Audit the exported derivations as well as the gated shallow proofs.
#print axioms Classicism.MathematicalContingency.rigid_representatives.derivable
#print axioms Classicism.MathematicalContingency.restricted_barcan.derivable
#print axioms Classicism.MathematicalContingency.restricted_barcan_dual.derivable
#print axioms Classicism.MathematicalContingency.local_selection.derivable
#print axioms Classicism.MathematicalContingency.local_selection_binary.derivable
#print axioms Classicism.MathematicalContingency.restricted_name_representation.derivable
