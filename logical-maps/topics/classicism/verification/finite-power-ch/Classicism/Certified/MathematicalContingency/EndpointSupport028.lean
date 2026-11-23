import Classicism.Certified.MathematicalContingency.EndpointAssembly32
import Classicism.Results.MathematicalContingency.FinitePowerCH
import Classicism.Tools.ReuseCertificate

import Classicism.Tools.DeepSplitTranslate

/-! Saved checkpoint-140 theorem values checked against native dependencies,
fresh current-statement quotations, and the C-minus axiom boundary.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.CertificateData.progress ".lake/finite-power-quotation-phases.log"

set_option Classicism.Meta.DeepSplitTranslate.profile true
set_option Classicism.Meta.DeepSplitTranslate.progress ".lake/finite-power-endpoint-progress.log"

-- No explicit checkpoint-140 certificate found for these targets.
#classicism_deep_split_derive Classicism.MathematicalContingency.lowerPeano_of_box
#print axioms Classicism.MathematicalContingency.lowerPeano_of_box.derivable

set_option Classicism.CertificateData.compositionalReflection true

#classicism_reuse_checkpoint
  "Classicism/Certified/MathematicalContingency/Checkpoint140/EndpointSupport028.json"
  Classicism.MathematicalContingency.entailment_counterexample_false
  Classicism.MathematicalContingency.outsideRigidPower_of_failure
  Classicism.MathematicalContingency.outsideRigidPower_coext
  Classicism.MathematicalContingency.rigid_subset_negative
  Classicism.MathematicalContingency.decisions_reconstruct
  Classicism.not_forall_eq

#print axioms Classicism.MathematicalContingency.entailment_counterexample_false.derivable
#print axioms Classicism.MathematicalContingency.entailment_counterexample_false.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.entailment_counterexample_false.reflect
#print axioms Classicism.MathematicalContingency.outsideRigidPower_of_failure.derivable
#print axioms Classicism.MathematicalContingency.outsideRigidPower_of_failure.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.outsideRigidPower_of_failure.reflect
#print axioms Classicism.MathematicalContingency.outsideRigidPower_coext.derivable
#print axioms Classicism.MathematicalContingency.outsideRigidPower_coext.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.outsideRigidPower_coext.reflect
#print axioms Classicism.MathematicalContingency.rigid_subset_negative.derivable
#print axioms Classicism.MathematicalContingency.rigid_subset_negative.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.rigid_subset_negative.reflect
#print axioms Classicism.MathematicalContingency.decisions_reconstruct.derivable
#print axioms Classicism.MathematicalContingency.decisions_reconstruct.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.decisions_reconstruct.reflect
#print axioms Classicism.not_forall_eq.derivable
#print axioms Classicism.not_forall_eq.checkpoint140_exact
#print axioms Classicism.not_forall_eq.reflect
