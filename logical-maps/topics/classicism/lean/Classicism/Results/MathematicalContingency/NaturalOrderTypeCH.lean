import Classicism.Results.MathematicalContingency.NaturalCohenCoordinates
import Classicism.Results.MathematicalContingency.OrderTypeCHBridge

/-! The negative order-type CH conclusion under the paper's boxed RC instances.
Section 1, Necessary Rigid Comprehension, assumes boxed RC for every finite
nonempty list of argument types. The Hartogs predicate instance is one of these.
All current RC inputs are obtained by box elimination; no local premise is
necessitated. Completion, natural rigidity and closed-segment premises stay explicit.
-/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ γ : Type} [Ty κ] [Ty γ]

theorem natural_cohen_possible_not_orderTypeCH
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
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → γ → Prop)
    (hH : CBA H R)
    (hc : DenseCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat e _)))) (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit) H R o C)
    (incompatible : IncompatibleCones (CohenCondition (HartogsCarrier (HartogsCarrier (@LowerNat e _))))
      (ConditionOrder LowerNat (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit) H R o C)
    (member : H o) (least : ∀ b, H b → R o b)
    (rigidN : Rigid (@LowerNat e _))
    (rcNames : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop)))
    (rcFreeze : □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop)))
    (rc : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcPair : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop)))
    (icPower : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → (((e → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop)))
    : ◇ (¬ Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) :=
  possible_not_equinumerous_hartogs_of_possible_not_cardinalCH
    (@LowerNat e _) (RigidPower (@LowerNat e _)) rc1
    (natural_cohen_possible_not_cardinalCH_of_closedSegments K L mp inaccessible
      (box_elim rcK) hi (box_elim rc1) (box_elim rp1) (box_elim rc2) (box_elim rp2)
      closed1 closed2 (box_elim rcC) H R o C hH hc incompatible member least rigidN
      (box_elim rcNames) (box_elim rcFreeze) rc ic (box_elim rcPair) icPower
      (box_elim rcNamePair))

#classicism_check natural_cohen_possible_not_orderTypeCH
#classicism_types natural_cohen_possible_not_orderTypeCH
end Classicism.MathematicalContingency
