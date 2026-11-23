import Classicism.Results.MathematicalContingency.HartogsCoordinates
import Classicism.Results.MathematicalContingency.HartogsPairing
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

/-- Eliminate the pairing and distinct-point witnesses before changing type. -/
theorem closedSegments_of_pairing_and_two (A : α → Prop)
    (pairing : ∃ Q, PairingOn A Q) (two : ∃ a b, A a ∧ A b ∧ a ≠ b) :
    ∀ m, HartogsCarrier A m →
      Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) m) A := by
  obtain ⟨Q,hq⟩ := pairing
  obtain ⟨a,b,ha,hb,hne⟩ := two
  exact hartogs_closedSegment_embeds A Q hq a b ha hb hne

/-- Pairing lifts using the first closed bound; two points lift along A -> H(A). -/
theorem hartogs_pairing_and_two (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (pairing : ∃ Q, PairingOn A Q)
    (two : ∃ a b, A a ∧ A b ∧ a ≠ b)
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rcPair : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop)) :
    (∃ R, PairingOn (HartogsCarrier A) R) ∧
      ∃ u v, HartogsCarrier A u ∧ HartogsCarrier A v ∧ u ≠ v := by
  have closed := closedSegments_of_pairing_and_two A pairing two
  obtain ⟨Q,hq⟩ := pairing
  obtain ⟨a,b,ha,hb,hne⟩ := two
  exact ⟨hartogs_pairing_of_closedSegments A rc rcPair Q hq closed,
    embeds_preserves_two A (HartogsCarrier A) (wellOrder_embeds_hartogs rc A L hw) a b ha hb hne⟩

/-- The second bound uses the pairing just constructed at H(A), so there is
no circular reliance on either closed-segment hypothesis. -/
theorem iterated_hartogs_closedSegments (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (pairing : ∃ Q, PairingOn A Q)
    (two : ∃ a b, A a ∧ A b ∧ a ≠ b)
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rcPair : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop)) :
    (∀ m, HartogsCarrier A m → Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) m) A) ∧
    (∀ m, HartogsCarrier (HartogsCarrier A) m →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier A)) (HartogsOrder (HartogsCarrier A)) m)
        (HartogsCarrier A)) := by
  have h := hartogs_pairing_and_two A L hw pairing two rc rcPair
  exact ⟨closedSegments_of_pairing_and_two A pairing two,
    closedSegments_of_pairing_and_two (HartogsCarrier A) h.1 h.2⟩

#classicism_check closedSegments_of_pairing_and_two hartogs_pairing_and_two iterated_hartogs_closedSegments
#classicism_types closedSegments_of_pairing_and_two hartogs_pairing_and_two iterated_hartogs_closedSegments
end Classicism.MathematicalContingency
