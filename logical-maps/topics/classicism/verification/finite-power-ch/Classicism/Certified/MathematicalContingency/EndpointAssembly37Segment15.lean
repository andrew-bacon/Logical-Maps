import Classicism.Certified.MathematicalContingency.EndpointAssembly37Segment14
import Classicism.Certified.MathematicalContingency.EndpointAssembly37ConversionRepair
import Classicism.Tools.SharedAssembly37

/-! Bounded, kernel-checked conversion continuation. Partial segments do not
assert the target. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Classicism.Meta.SharedAssembly37.profile true
set_option Classicism.Meta.SharedAssembly37.progress ".lake/finite-power-endpoint-progress.log"
set_option Classicism.Meta.SharedAssembly37.conversionTrace ".lake/finite-power-assembly37-segment15-shared.log"
set_option Classicism.Meta.ConversionCache.progress ".lake/finite-power-assembly37-cache-segment15-shared.log"
#classicism_staged_shared37_derive Classicism.MathematicalContingency.FinitePower.negative_possible_not_cardinalCH 50
run_cmd do
  IO.FS.withFile ".lake/finite-power-quotation-phases.log" .append fun h => do
    h.putStrLn s!"{← IO.monoMsNow} bounded conversion segment complete; awaiting export"
