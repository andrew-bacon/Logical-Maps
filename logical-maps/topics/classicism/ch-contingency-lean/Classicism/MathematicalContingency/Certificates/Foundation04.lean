import Classicism.MathematicalContingency.Arithmetic
import Classicism.MathematicalContingency.CardinalPower
import Classicism.MathematicalContingency.CantorBernstein
import Classicism.MathematicalContingency.Hartogs
import Classicism.MathematicalContingency.OrderComparison
import Classicism.Tools.Translate
import Classicism.MathematicalContingency.Certificates.Foundation03
/-! Original foundation certificate, split to bound memory.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.lowerProd_total
#print axioms Classicism.MathematicalContingency.lowerProd_total.derivable
