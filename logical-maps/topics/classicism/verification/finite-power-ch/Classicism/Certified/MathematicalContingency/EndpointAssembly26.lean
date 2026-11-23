import Classicism.Certified.MathematicalContingency.EndpointAssembly26Proof
import Classicism.Certified.MathematicalContingency.EndpointAssembly26Statement
import Classicism.Tools.DeepSplitTranslate

/-! Closed derivations needed by the Finite-Power CH endpoint.
Only missing derivations in its proof dependency closure are generated here.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
set_option Classicism.Meta.SharedClosedQuote.phaseFile ".lake/finite-power-quotation-phases.log"
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.Meta.DeepSplitTranslate.profile true
set_option Classicism.Meta.DeepSplitTranslate.progress ".lake/finite-power-endpoint-progress.log"
set_option Classicism.Meta.DeepSplitTranslate.conversionTrace ".lake/finite-power-conversion-progress.log"

-- Quote the original statement independently, then require the generic proof
-- to inhabit exactly that object-language theorem. This is a checked proof
-- replacement, not an axiom or an additional hypothesis.

#classicism_quote_phase Classicism.MathematicalContingency.FinitePower.negative_MP_realization "checking original-statement derivation bridge"

namespace Classicism.MathematicalContingency.FinitePower
theorem negative_MP_realization.derivable :
    Classicism.Meta.Theorem
      (Classicism.Meta.C.axiomsMinus (Sig := Classicism.Meta.Signature.pure))
      negative_MP_realization.quoted :=
  negative_MP_realization_via_generic.derivable
end Classicism.MathematicalContingency.FinitePower

#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.reflect
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.quoted_closedTypes
#classicism_deep_split_derive Classicism.MathematicalContingency.FinitePower.negative_MP_realization
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.derivable

#classicism_quote_phase Classicism.MathematicalContingency.FinitePower.negative_MP_realization "derivation bridge and axiom audits finished; module export pending"
