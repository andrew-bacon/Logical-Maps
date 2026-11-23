import Classicism.Certified.MathematicalContingency.EndpointSupport048
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

run_cmd Lean.Elab.Command.liftTermElabM (Classicism.CertificateData.importTheorems "Classicism/Certified/MathematicalContingency/Checkpoint140/EndpointSupport049.json")
#print axioms Classicism.MathematicalContingency.finiteTernary_image.derivable
#print axioms Classicism.MathematicalContingency.ternaryImage_reflect.derivable
#print axioms Classicism.MathematicalContingency.ternaryImage_rigid_injective.derivable
#print axioms Classicism.MathematicalContingency.rigidFiniteTernary_embeds_finitePower.derivable
#print axioms Classicism.MathematicalContingency.finiteCondition_embeds_finitePower.derivable
#print axioms Classicism.MathematicalContingency.finiteCondition_cardinal_bound.derivable

run_cmd do
  IO.FS.withFile ".lake/finite-power-quotation-phases.log" .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} source statement and axiom commands complete; awaiting module export"
