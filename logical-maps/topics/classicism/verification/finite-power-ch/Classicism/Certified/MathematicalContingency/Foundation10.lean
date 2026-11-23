import Classicism.Results.MathematicalContingency.Arithmetic
import Classicism.Results.MathematicalContingency.CardinalPower
import Classicism.Results.MathematicalContingency.CantorBernstein
import Classicism.Results.MathematicalContingency.Hartogs
import Classicism.Results.MathematicalContingency.OrderComparison
import Classicism.Tools.Translate
import Classicism.Certified.MathematicalContingency.Foundation09
/-! Original foundation certificate, split to bound memory.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.no_embedding_into_proper_segment
#print axioms Classicism.MathematicalContingency.no_embedding_into_proper_segment.derivable
