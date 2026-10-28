import Classicism.MathematicalContingency.Arithmetic
import Classicism.MathematicalContingency.CardinalPower
import Classicism.MathematicalContingency.CantorBernstein
import Classicism.MathematicalContingency.Hartogs
import Classicism.MathematicalContingency.OrderComparison
import Classicism.Tools.Translate
/-! Original foundation certificate, split to bound memory.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.lowerNat_induction
#print axioms Classicism.MathematicalContingency.lowerNat_induction.derivable
