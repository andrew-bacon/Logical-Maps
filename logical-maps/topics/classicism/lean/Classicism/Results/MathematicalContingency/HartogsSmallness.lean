import Classicism.Results.MathematicalContingency.SegmentSmallness
import Classicism.Results.MathematicalContingency.HartogsTheorem

/-!
Hartogs preserves smallness below a well-ordered strong-limit bound.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Only certified proper-segment results are used; the deferred closed-segment
lemma and the pending HartogsBounds/IndexCardinality chains are not used.
-/
namespace Classicism.MathematicalContingency
variable {κ α : Type} [Ty κ] [Ty α]

theorem small_hartogs (K : κ → Prop) (L : κ → κ → Prop)
    (hk : WellOrderOn K L) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop))
    (A : α → Prop) (rcA : P.RigidComprehension (α → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier α → Prop))
    (small : Small K L A) : Small K L (HartogsCarrier A) :=
  small_of_segment_bounds K L hk limit rcK A rcA
    (HartogsCarrier A) (HartogsOrder A) (hartogs_wellOrder rcH A)
    (hartogs_segment_embeds A) small

theorem small_doubleHartogs (K : κ → Prop) (L : κ → κ → Prop)
    (hk : WellOrderOn K L) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop))
    (A : α → Prop) (rcA : P.RigidComprehension (α → Prop))
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (small : Small K L A) : Small K L (HartogsCarrier (HartogsCarrier A)) :=
  small_hartogs K L hk limit rcK (HartogsCarrier A) rc1 rc2
    (small_hartogs K L hk limit rcK A rcA rc1 small)

#classicism_check small_hartogs small_doubleHartogs
#classicism_types small_hartogs small_doubleHartogs
end Classicism.MathematicalContingency
