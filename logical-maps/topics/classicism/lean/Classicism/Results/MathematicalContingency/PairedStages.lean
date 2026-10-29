import Classicism.Results.MathematicalContingency.HartogsCoordinates
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]
/-- Compose two conditional pairing constructions before high-type substitution. -/
theorem pairing_two_stages (A : α → Prop) (H : β → Prop) (J : γ → Prop)
    (L : β → β → Prop) (M : γ → γ → Prop)
    (Q : α → α → α → Prop) (pair : PairingOn A Q)
    (hw : WellOrderOn H L) (jw : WellOrderOn J M)
    (gapH : ¬ Embeds H A) (gapJ : ¬ Embeds J H)
    (closedH : ∀ h, H h → Embeds (ClosedSegment H L h) A)
    (closedJ : ∀ j, J j → Embeds (ClosedSegment J M j) H)
    (rcH : P.RigidComprehension (β → β → Prop))
    (rcJ : P.RigidComprehension (γ → γ → Prop)) : ∃ R, PairingOn J R := by
  obtain ⟨R,hr⟩ := pairing_of_closedSegment_bounds A H L Q hw pair gapH closedH rcH
  exact pairing_of_closedSegment_bounds H J M R jw hr gapJ closedJ rcJ
#classicism_check pairing_two_stages
#classicism_types pairing_two_stages
end Classicism.MathematicalContingency
