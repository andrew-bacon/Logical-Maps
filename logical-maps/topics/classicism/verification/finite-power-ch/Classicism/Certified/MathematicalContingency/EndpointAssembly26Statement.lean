import Classicism.Certified.MathematicalContingency.EndpointAssembly26Piece0
import Classicism.Certified.MathematicalContingency.EndpointAssembly26Piece1
import Classicism.Certified.MathematicalContingency.EndpointAssembly26Piece2
import Classicism.Certified.MathematicalContingency.EndpointAssembly26Piece3
import Classicism.Certified.MathematicalContingency.EndpointAssembly26Piece4

/-! Assemble independently checked reflection components, with a separate
literal comparison to the unchanged original native quotation.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
set_option Classicism.Meta.SharedClosedQuote.phaseFile ".lake/finite-power-quotation-phases.log"

#classicism_quote_phase Classicism.MathematicalContingency.FinitePower.negative_MP_realization "assembling full original statement"
#classicism_shared_quote_assemble Classicism.MathematicalContingency.FinitePower.negative_MP_realization
#classicism_quote_phase Classicism.MathematicalContingency.FinitePower.negative_MP_realization "full quotation and reflection checked; checking closed types"

theorem Classicism.MathematicalContingency.FinitePower.negative_MP_realization.quoted_closedTypes :
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.quoted.closedTypes = true := by
  simp only [Classicism.MathematicalContingency.FinitePower.negative_MP_realization.quoted, Classicism.Meta.Term.closedTypes_imp,
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece0.quoted_closedTypes,
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece1.quoted_closedTypes,
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece2.quoted_closedTypes,
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece3.quoted_closedTypes,
    Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.quoted_closedTypes]
  rfl

#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.reflect
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.quotation_agreement
#print axioms Classicism.MathematicalContingency.FinitePower.negative_MP_realization.quoted_closedTypes

#classicism_quote_phase Classicism.MathematicalContingency.FinitePower.negative_MP_realization "statement audits finished; module export pending"
