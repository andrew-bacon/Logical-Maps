import Classicism.Results.MathematicalContingency.NaturalCohenCH
import Classicism.Results.MathematicalContingency.HartogsCoordinates
/-! Discharge the coordinate package using the existing closed-segment assumptions. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ γ : Type} [Ty κ] [Ty γ]

theorem natural_cohen_possible_not_cardinalCH_of_closedSegments
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt γ K L)
    (inaccessible : StronglyInaccessible K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity e)
    (rc1 : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (closed1 : ∀ h, HartogsCarrier (@LowerNat e _) h → Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) h) (@LowerNat e _))
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier (@LowerNat e _)) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier (@LowerNat e _))) (HartogsOrder (HartogsCarrier (@LowerNat e _))) j) (HartogsCarrier (@LowerNat e _)))
    (rcC : Classicism.P.RigidComprehension (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)))))
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → γ → Prop)
    (hH : CBA H R)
    (hc : DenseCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat e _)))) (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit) H R o C)
    (incompatible : IncompatibleCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat e _))))
      (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit) H R o C)
    (member : H o) (least : ∀ b, H b → R o b)
    (rigidN : Rigid (@LowerNat e _))
    (rcNames : Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop))
    (rc : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → (((e → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    : ◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) :=
  natural_cohen_possible_not_cardinalCH K L mp inaccessible rcK hi rc1 rp1 rc2 rp2
    closed1 closed2 rcC H R o C hH hc incompatible member least rigidN rcNames
    rcFreeze rc ic rcPair icPower rcNamePair
    (natural_hartogs_coordinate_bounds (lowerPeano_of_box hi) rc1 rp1 rc2 closed1)

#classicism_check natural_cohen_possible_not_cardinalCH_of_closedSegments
#classicism_types natural_cohen_possible_not_cardinalCH_of_closedSegments
end Classicism.MathematicalContingency
