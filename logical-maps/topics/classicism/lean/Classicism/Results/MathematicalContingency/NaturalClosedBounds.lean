import Classicism.Results.MathematicalContingency.HartogsClosedBounds
import Classicism.Results.MathematicalContingency.RegularOpenCH
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem lowerNat_pairing_and_two (hp : LowerPeano σ) :
    (∃ Q, PairingOn (@LowerNat σ _) Q) ∧
      ∃ (a b : (σ → Prop) → Prop), LowerNat a ∧ LowerNat b ∧ a ≠ b :=
  ⟨⟨LowerPair,lowerPair_pairing hp⟩,AtLeastZero σ,SucCard (AtLeastZero σ),
    lowerNat_zero,lowerNat_suc _ lowerNat_zero,lowerNat_ne_suc_self hp _ lowerNat_zero⟩

/-- The exact two bounds consumed by the CH construction, with no rigidity premise. -/
theorem natural_hartogs_closedSegments (hp : LowerPeano e)
    (rc : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)) :
    NaturalCHClosedSegments :=
  iterated_hartogs_closedSegments LowerNat LowerLT (lowerNat_wellOrder hp)
    (lowerNat_pairing_and_two hp).1 (lowerNat_pairing_and_two hp).2 rc rcPair

#classicism_check lowerNat_pairing_and_two natural_hartogs_closedSegments
#classicism_types lowerNat_pairing_and_two natural_hartogs_closedSegments
end Classicism.MathematicalContingency
