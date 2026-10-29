import Classicism.Results.MathematicalContingency.CommonPairedBound
/-! Separate the two constructions before assembling the common bound.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

theorem doubleHartogs_embeds_base (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L)
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop)) :
    Embeds A (HartogsCarrier (HartogsCarrier A)) :=
  embeds_trans A (HartogsCarrier A) (HartogsCarrier (HartogsCarrier A))
    (wellOrder_embeds_hartogs rc1 A L hw)
    (wellOrder_embeds_hartogs rc2 (HartogsCarrier A) (HartogsOrder A) (hartogs_wellOrder rc1 A))

theorem doubleHartogs_pairing_closed (A : α → Prop)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → OrdinalCarrier (OrdinalCarrier α) → Prop))
    (closed1 : ∀ h, HartogsCarrier A h → Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) h) A)
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier A) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier A)) (HartogsOrder (HartogsCarrier A)) j) (HartogsCarrier A)) :
    ∃ R, PairingOn (HartogsCarrier (HartogsCarrier A)) R := by
  obtain ⟨R,hr⟩ := hartogs_pairing_of_closedSegments A rc1 rp1 Q hq closed1
  exact hartogs_pairing_of_closedSegments (HartogsCarrier A) rc2 rp2 R hr closed2

#classicism_check doubleHartogs_embeds_base doubleHartogs_pairing_closed
#classicism_types doubleHartogs_embeds_base doubleHartogs_pairing_closed
end Classicism.MathematicalContingency
