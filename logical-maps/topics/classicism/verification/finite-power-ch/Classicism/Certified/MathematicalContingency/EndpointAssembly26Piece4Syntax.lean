import Classicism.Results.MathematicalContingency.SmallForcingCompletions
import Classicism.Tools.SplitClosedQuote
import Classicism.Syntax.ClosedTypes

/-! Save the native quotation and its closed-type proof independently.
No reflection of the complete conclusion is claimed in this module.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
set_option Classicism.Meta.SharedClosedQuote.splitReflection true
set_option Classicism.Meta.SharedClosedQuote.phaseFile ".lake/finite-power-quotation-phases.log"

#classicism_shared_quote_piece_syntax Classicism.MathematicalContingency.FinitePower.negative_MP_realization 4
theorem Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.quoted_closedTypes :
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.quoted.closedTypes = true := by
  simp [Classicism.Meta.Term.closedTypes]

#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.quotation_agreement
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.quoted_closedTypes
