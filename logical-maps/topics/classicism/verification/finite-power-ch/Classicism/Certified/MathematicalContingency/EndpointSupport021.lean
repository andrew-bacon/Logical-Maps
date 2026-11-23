import Classicism.Certified.MathematicalContingency.EndpointAssembly26
import Classicism.Results.MathematicalContingency.FinitePowerCH
import Classicism.Tools.ReuseCertificate

/-! The five saved checkpoint-140 proof terms are checked against native
declarations and fresh quotations of the current source statements. No old
project or foundations are imported, and no old proof generator is rerun.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8

#classicism_reuse_checkpoint
  "Classicism/Certified/MathematicalContingency/Checkpoint140/BooleanDecisions.json"
  Classicism.MathematicalContingency.cba_meet_exists
  Classicism.MathematicalContingency.meet_top_self
  Classicism.MathematicalContingency.cba_disjoint_complement
  Classicism.MathematicalContingency.cba_nonzero_decision
  Classicism.MathematicalContingency.decidesAt_down

#print axioms Classicism.MathematicalContingency.cba_meet_exists.derivable
#print axioms Classicism.MathematicalContingency.meet_top_self.derivable
#print axioms Classicism.MathematicalContingency.cba_disjoint_complement.derivable
#print axioms Classicism.MathematicalContingency.cba_nonzero_decision.derivable
#print axioms Classicism.MathematicalContingency.decidesAt_down.derivable
