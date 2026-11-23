import Classicism.Certified.MathematicalContingency.EndpointSupport043
import Classicism.Results.MathematicalContingency.FinitePowerCH
import Classicism.Tools.ReuseCertificate

/-! Bounded native reuse of checkpoint-140 theorem values.
Partial reflections do not assert a completed current-statement certificate.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
set_option Classicism.CertificateData.progress ".lake/finite-power-quotation-phases.log"

run_cmd Lean.Elab.Command.liftTermElabM (Classicism.CertificateData.importTheorems "Classicism/Certified/MathematicalContingency/Checkpoint140/EndpointSupport044.json")
#print axioms Classicism.MathematicalContingency.ordLim_stableApplication.derivable
#print axioms Classicism.MathematicalContingency.ordinal_stableApplication.derivable
#print axioms Classicism.MathematicalContingency.ordinal_application_negative.derivable
#print axioms Classicism.MathematicalContingency.ordinal_application_persistent.derivable
#print axioms Classicism.MathematicalContingency.stable_exactOrdinal_distinct.derivable
#print axioms Classicism.MathematicalContingency.hartogsCarrier_nd.derivable

run_cmd do
  IO.FS.withFile ".lake/finite-power-quotation-phases.log" .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} source statement and axiom commands complete; awaiting module export"
