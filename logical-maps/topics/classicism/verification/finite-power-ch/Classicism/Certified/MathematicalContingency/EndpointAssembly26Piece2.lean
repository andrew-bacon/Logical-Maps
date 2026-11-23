import Classicism.Results.MathematicalContingency.SmallForcingCompletions
import Classicism.Tools.SplitClosedQuote
import Classicism.Syntax.ClosedTypes

/-! A separately compiled component of the original negative-realization
statement. This proves reflection, not the truth of the component.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
set_option Classicism.Meta.SharedClosedQuote.splitReflection true
set_option Classicism.Meta.SharedClosedQuote.phaseFile ".lake/finite-power-quotation-phases.log"

#classicism_shared_quote_piece Classicism.MathematicalContingency.FinitePower.negative_MP_realization 2
theorem Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece2.quoted_closedTypes :
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece2.quoted.closedTypes = true := by
  simp [Classicism.Meta.Term.closedTypes]

#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece2.reflect
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece2.quotation_agreement
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece2.quoted_closedTypes
