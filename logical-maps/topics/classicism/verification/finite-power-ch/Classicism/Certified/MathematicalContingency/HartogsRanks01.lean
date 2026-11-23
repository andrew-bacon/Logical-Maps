import Classicism.Results.MathematicalContingency.HartogsRanks
import Classicism.Certified.MathematicalContingency.OrdinalUniqueness10
/-! One theorem per file to bound certificate-generation memory. -/
/- The proof transports upward properties; it does not use order trichotomy.
Keep that unrelated certificate chain outside this focused dependency graph.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 8
#classicism_derive Classicism.MathematicalContingency.exactOrdinal_iso
#print axioms Classicism.MathematicalContingency.exactOrdinal_iso.derivable
