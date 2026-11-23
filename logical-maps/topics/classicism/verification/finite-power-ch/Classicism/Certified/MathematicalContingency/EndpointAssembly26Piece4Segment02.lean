import Classicism.Certified.MathematicalContingency.EndpointAssembly26Piece4Segment01

/-! Continue from exported, kernel-checked equalities. The final reflection is
claimed only if the compositional proof finishes in this batch.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
set_option Classicism.Meta.SharedClosedQuote.phaseFile ".lake/finite-power-quotation-phases.log"
#classicism_shared_reflect_segment Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4 4000
run_cmd do
  let n := if (← Lean.getEnv).contains `Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.reflect then
    `Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.reflect else `Classicism.MathematicalContingency.FinitePower.negative_MP_realization.piece4.reflectionPieces.step7999
  Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
