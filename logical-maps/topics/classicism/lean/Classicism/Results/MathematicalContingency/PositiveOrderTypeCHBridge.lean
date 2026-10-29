import Classicism.Results.MathematicalContingency.OrderTypeCHBridge
import Classicism.Results.MathematicalContingency.WellOrderPullback
import Classicism.Results.MathematicalContingency.CardinalPower

/-! A target for the positive forcing branch: embedding the continuum into a
countable-segment well-order suffices. The index need not remain uncountable. -/
namespace Classicism.MathematicalContingency
variable {α β γ δ : Type} [Ty α] [Ty β] [Ty γ] [Ty δ]

theorem equinumerous_of_embeds_countable_segments
    (N : α → Prop) (S : β → Prop) (A : γ → Prop) (L : γ → γ → Prop)
    (H : δ → Prop) (M : δ → δ → Prop)
    (ha : WellOrderOn A L) (hh : WellOrderOn H M)
    (smallA : ∀ a, A a → Embeds (Segment A L a) N)
    (smallH : ∀ h, H h → Embeds (Segment H M h) N)
    (largeS : ¬ Embeds S N) (largeH : ¬ Embeds H N) (bound : Embeds S A) :
    Equinumerous S H := by
  obtain ⟨R,hs⟩ := wellOrder_exists_of_embeds S A L ha bound
  exact cantor_bernstein S H
    (embeds_trans S A H bound
      (wellOrder_embeds_from_segment_bounds N A L H M ha hh largeH smallA))
    (wellOrder_embeds_from_segment_bounds N H M S R hh hs largeS smallH)

theorem rigidPower_equinumerous_hartogs_of_embeds
    (N : α → Prop) (A : β → Prop) (L : β → β → Prop)
    (rcN : P.RigidComprehension (α → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier α → Prop))
    (ha : WellOrderOn A L) (small : ∀ a, A a → Embeds (Segment A L a) N)
    (bound : Embeds (RigidPower N) A) : Equinumerous (RigidPower N) (HartogsCarrier N) :=
  equinumerous_of_embeds_countable_segments N (RigidPower N) A L
    (HartogsCarrier N) (HartogsOrder N) ha (hartogs_wellOrder rcH N)
    small (hartogs_segment_embeds N) (rigidPower_not_embeds rcN N)
    (inductive_hartogs rcH N).2.1 bound

/-- Only the embedding is asserted possible; all structural inputs are boxed. -/
theorem possible_rigidPower_equinumerous_hartogs_of_possible_embeds
    (N : α → Prop) (A : β → Prop) (L : β → β → Prop)
    (rcN : □ (P.RigidComprehension (α → Prop)))
    (rcH : □ (P.RigidComprehension (OrdinalCarrier α → Prop)))
    (ha : □ (WellOrderOn A L))
    (small : □ (∀ a, A a → Embeds (Segment A L a) N))
    (bound : ◇ (Embeds (RigidPower N) A)) :
    ◇ (Equinumerous (RigidPower N) (HartogsCarrier N)) :=
  dia_mono _ _
    (modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (rn : P.RigidComprehension (α → Prop))
        (rh : P.RigidComprehension (OrdinalCarrier α → Prop))
        (hw : WellOrderOn A L) (hs : ∀ a, A a → Embeds (Segment A L a) N)
        (hb : Embeds (RigidPower N) A) =>
        rigidPower_equinumerous_hartogs_of_embeds N A L rn rh hw hs hb)) rcN) rcH) ha) small)
    bound

#classicism_check equinumerous_of_embeds_countable_segments rigidPower_equinumerous_hartogs_of_embeds possible_rigidPower_equinumerous_hartogs_of_possible_embeds
#classicism_types equinumerous_of_embeds_countable_segments rigidPower_equinumerous_hartogs_of_embeds possible_rigidPower_equinumerous_hartogs_of_possible_embeds
end Classicism.MathematicalContingency
