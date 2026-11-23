import Classicism.Certified.MathematicalContingency.EndpointSupport026
import Classicism.Results.MathematicalContingency.FinitePowerCH
import Classicism.Tools.ReuseCertificate

/-! Saved checkpoint-140 theorem values checked against native dependencies,
fresh current-statement quotations, and the C-minus axiom boundary.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.CertificateData.progress ".lake/finite-power-quotation-phases.log"

set_option Classicism.CertificateData.compositionalReflection true

#classicism_reuse_checkpoint
  "Classicism/Certified/MathematicalContingency/Checkpoint140/EndpointSupport027.json"
  Classicism.MathematicalContingency.intervalIso_meet_zero
  Classicism.MathematicalContingency.intervalIso_decision
  Classicism.MathematicalContingency.binaryDecisions_local

#print axioms Classicism.MathematicalContingency.intervalIso_meet_zero.derivable
#print axioms Classicism.MathematicalContingency.intervalIso_meet_zero.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.intervalIso_meet_zero.reflect
#print axioms Classicism.MathematicalContingency.intervalIso_decision.derivable
#print axioms Classicism.MathematicalContingency.intervalIso_decision.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.intervalIso_decision.reflect
#print axioms Classicism.MathematicalContingency.binaryDecisions_local.derivable
#print axioms Classicism.MathematicalContingency.binaryDecisions_local.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.binaryDecisions_local.reflect
