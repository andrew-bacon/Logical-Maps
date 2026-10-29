import Classicism.Results.MathematicalContingency.SmallnessTransfer
import Classicism.Results.MathematicalContingency.WellOrderCardinality
import Classicism.Results.MathematicalContingency.CardinalPower

/-!
Smallness from well-order comparison and bounds on proper segments.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
All carriers are arbitrary admissible types. No regularity, initial-cardinality,
closed-segment bound, carrier rigidity or choice premise is used.
-/
namespace Classicism.MathematicalContingency
variable {κ α β : Type} [Ty κ] [Ty α] [Ty β]

theorem small_of_wellOrder_not_embeds (K : κ → Prop) (L : κ → κ → Prop)
    (A : α → Prop) (R : α → α → Prop) (hk : WellOrderOn K L)
    (ha : WellOrderOn A R) (gap : ¬ Embeds K A) : Small K L A := by
  obtain ⟨a,ha,F,hF⟩ := wellOrder_proper_segment_of_not_embeds A R K L ha hk gap
  exact ⟨a,ha,F,hF.1.1⟩

/-- A small rigid power bounds every well-order whose proper segments embed
into its base. Cantor rules out the reverse comparison. -/
theorem small_of_power_and_segment_bounds (K : κ → Prop) (L : κ → κ → Prop)
    (hk : WellOrderOn K L) (A : α → Prop)
    (rcA : P.RigidComprehension (α → Prop))
    (H : β → Prop) (R : β → β → Prop) (hw : WellOrderOn H R)
    (segments : ∀ h, H h → Embeds (Segment H R h) A)
    (power : Small K L (RigidPower A)) : Small K L H := by
  obtain ⟨a,ha,bound⟩ := power
  have gap : ¬ Embeds (Segment K L a) A :=
    fun reverse => (cantor_rigidPower rcA A).2
      (embeds_trans (RigidPower A) (Segment K L a) A bound reverse)
  exact ⟨a,ha,wellOrder_embeds_from_segment_bounds A H R
    (Segment K L a) (RestrictOrder L (Segment K L a)) hw
    (wellOrder_restrict K (Segment K L a) L hk (fun _ h => h.1)) gap segments⟩

theorem small_of_segment_bounds (K : κ → Prop) (L : κ → κ → Prop)
    (hk : WellOrderOn K L) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop))
    (A : α → Prop) (rcA : P.RigidComprehension (α → Prop))
    (H : β → Prop) (R : β → β → Prop) (hw : WellOrderOn H R)
    (segments : ∀ h, H h → Embeds (Segment H R h) A)
    (small : Small K L A) : Small K L H :=
  small_of_power_and_segment_bounds K L hk A rcA H R hw segments
    (small_rigidPower K L limit rcK A small)

#classicism_check small_of_wellOrder_not_embeds small_of_power_and_segment_bounds small_of_segment_bounds
#classicism_types small_of_wellOrder_not_embeds small_of_power_and_segment_bounds small_of_segment_bounds
end Classicism.MathematicalContingency
