import Classicism.Certified.MathematicalContingency.EndpointSupport042Raw

/-! Bounded native reuse of checkpoint-140 theorem values.
Partial reflections do not assert a completed current-statement certificate.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.CertificateData.progress ".lake/finite-power-quotation-phases.log"

set_option Classicism.CertificateData.compositionalReflection false
run_cmd Lean.Elab.Command.liftTermElabM (Classicism.CertificateData.checkCurrentStatement ``Classicism.weaklyPersistent_of_persistent)
#print axioms Classicism.weaklyPersistent_of_persistent.derivable
#print axioms Classicism.weaklyPersistent_of_persistent.checkpoint140_exact
#print axioms Classicism.weaklyPersistent_of_persistent.reflect
run_cmd Lean.logInfo "shared dependency current-statement audit: Classicism.weaklyPersistent_of_persistent"
run_cmd Lean.Elab.Command.liftTermElabM (Classicism.CertificateData.checkCurrentStatement ``Classicism.weaklyInextensible_of_inextensible)
#print axioms Classicism.weaklyInextensible_of_inextensible.derivable
#print axioms Classicism.weaklyInextensible_of_inextensible.checkpoint140_exact
#print axioms Classicism.weaklyInextensible_of_inextensible.reflect
run_cmd Lean.logInfo "shared dependency current-statement audit: Classicism.weaklyInextensible_of_inextensible"
run_cmd Lean.Elab.Command.liftTermElabM (Classicism.CertificateData.checkCurrentStatement ``Classicism.weaklyRigid_of_rigid)
#print axioms Classicism.weaklyRigid_of_rigid.derivable
#print axioms Classicism.weaklyRigid_of_rigid.checkpoint140_exact
#print axioms Classicism.weaklyRigid_of_rigid.reflect
run_cmd Lean.logInfo "shared dependency current-statement audit: Classicism.weaklyRigid_of_rigid"

run_cmd do
  IO.FS.withFile ".lake/finite-power-quotation-phases.log" .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} source statement and axiom commands complete; awaiting module export"
