import Classicism.Certified.MathematicalContingency.EndpointSupport031C
import Classicism.Results.MathematicalContingency.FinitePowerCH
import Classicism.Tools.ReuseCertificate

/-! Checkpoint-140 reuse split after the combined module exceeded its RSS guard.
Each statement retains its native kernel, exact-quotation and axiom audits.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.CertificateData.progress ".lake/finite-power-quotation-phases.log"
set_option Classicism.CertificateData.compositionalReflection true

run_cmd Lean.Elab.Command.liftTermElabM (Classicism.CertificateData.checkCurrentStatement ``Classicism.MathematicalContingency.supremum_unique)
#print axioms Classicism.MathematicalContingency.supremum_unique.derivable
#print axioms Classicism.MathematicalContingency.supremum_unique.checkpoint140_exact
#print axioms Classicism.MathematicalContingency.supremum_unique.reflect

run_cmd do
  IO.FS.withFile ".lake/finite-power-quotation-phases.log" .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} source statement and axiom commands complete; awaiting module export"
