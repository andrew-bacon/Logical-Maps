import Classicism.Results.MathematicalContingency.HartogsIndices

/-! Cross-type cardinal bounds from Hartogs comparison.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem wellOrder_embeds_hartogs_of_segments
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (A : α → Prop) (B : β → Prop) (L : β → β → Prop) (hw : WellOrderOn B L)
    (small : ∀ b, B b → Embeds (Segment B L b) A) : Embeds B (HartogsCarrier A) := by
  exact wellOrder_embeds_from_segment_bounds A B L (HartogsCarrier A) (HartogsOrder A)
    hw (hartogs_wellOrder rc A) (inductive_hartogs rc A).2.1 small

theorem wellOrder_small_or_hartogs_below
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (A : α → Prop) (B : β → Prop) (L : β → β → Prop) (hw : WellOrderOn B L) :
    Embeds B A ∨ Embeds (HartogsCarrier A) B := by
  exact wellOrder_small_or_larger A B L (HartogsCarrier A) (HartogsOrder A)
    hw (hartogs_wellOrder rc A) (hartogs_segment_embeds A)

theorem smaller_hartogs_iff_embeds
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (A : α → Prop) (B : β → Prop) (L : β → β → Prop) (hw : WellOrderOn B L)
    (hA : Embeds A (HartogsCarrier A)) : Smaller B (HartogsCarrier A) ↔ Embeds B A := by
  constructor
  · intro h
    exact (wellOrder_small_or_hartogs_below rc A B L hw).elim id (fun k => (h.2 k).elim)
  · intro h
    exact ⟨embeds_trans B A _ h hA,fun k => (inductive_hartogs rc A).2.1 (embeds_trans _ B A k h)⟩

#classicism_check wellOrder_embeds_hartogs_of_segments wellOrder_small_or_hartogs_below smaller_hartogs_iff_embeds
#classicism_types wellOrder_embeds_hartogs_of_segments wellOrder_small_or_hartogs_below smaller_hartogs_iff_embeds
end Classicism.MathematicalContingency
