import Classicism.Results.MathematicalContingency.NaturalPositiveCH
import Classicism.Results.MathematicalContingency.NaturalOrderTypeCH

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

def NaturalCohenCompletion : Prop :=
  ∃ (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → γ → Prop),
    CBA H R ∧
    DenseCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat e _)))) (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit) H R o C ∧
    IncompatibleCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat e _)))) (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit) H R o C ∧
    H o ∧ (∀ b, H b → R o b)

theorem natural_cohen_completion_possible_not_CH
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt γ K L)
    (inaccessible : StronglyInaccessible K L) (rcK : □ (Classicism.P.RigidComprehension (κ → Prop)))
    (hi : DraftBoxInfinity e)
    (rc1 : □ (P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop)))
    (rp1 : □ (P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)))
    (rc2 : □ (P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop)))
    (rp2 : □ (P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop)))
    (closed1 : ∀ h, HartogsCarrier (@LowerNat e _) h → Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) h) (@LowerNat e _))
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier (@LowerNat e _)) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier (@LowerNat e _))) (HartogsOrder (HartogsCarrier (@LowerNat e _))) j) (HartogsCarrier (@LowerNat e _)))
    (rcC : □ (Classicism.P.RigidComprehension (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))))))
    (completion : NaturalCohenCompletion (γ := γ))
    (rigidN : Rigid (@LowerNat e _))
    (rcNames : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop)))
    (rcFreeze : □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop)))
    (rc : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcPair : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop)))
    (icPower : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → (((e → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop)))
    : (◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _)))) ∧
      ◇ (¬ Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) := by
  obtain ⟨H,R,o,C,hH,hc,incompatible,member,least⟩ := completion
  have hn := natural_cohen_possible_not_cardinalCH_of_closedSegments K L mp inaccessible
    (box_elim rcK) hi (box_elim rc1) (box_elim rp1) (box_elim rc2) (box_elim rp2)
    closed1 closed2 (box_elim rcC) H R o C hH hc incompatible member least rigidN
    (box_elim rcNames) (box_elim rcFreeze) rc ic (box_elim rcPair) icPower (box_elim rcNamePair)
  exact ⟨hn,possible_not_equinumerous_hartogs_of_possible_not_cardinalCH
    LowerNat (RigidPower LowerNat) rc1 hn⟩

#classicism_check natural_cohen_completion_possible_not_CH
#classicism_types natural_cohen_completion_possible_not_CH
end Classicism.MathematicalContingency
