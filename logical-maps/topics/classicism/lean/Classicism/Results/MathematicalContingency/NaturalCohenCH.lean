import Classicism.Results.MathematicalContingency.CohenCommonBound
import Classicism.Results.MathematicalContingency.NaturalCommonBound

/-! Specialize the Cohen argument using the certified natural double-Hartogs bound.
The coordinate and completion inputs remain explicit; no new deferral is introduced. -/
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ γ : Type} [Ty κ] [Ty γ]

theorem natural_cohen_possible_not_cardinalCH
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
    (coordinates : ∃ I₁ L₁ Q₁, CohenCoordinateBounds (@LowerNat e _) (HartogsCarrier (HartogsCarrier (@LowerNat e _))) I₁ L₁ Q₁) :
    ◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) := by
  have bound := natural_small_commonPairedBound K L inaccessible (lowerPeano_of_box hi)
    rcK (box_elim rc) rc1 rp1 rc2 rp2 closed1 closed2
  exact cohen_possible_not_cardinalCH_of_common_bound K L mp inaccessible.2.2.2 rcK hi
    (HartogsCarrier (HartogsCarrier (@LowerNat e _))) rcC rc2 bound.1 H R o C hH hc
    incompatible bound.2 member least rigidN rcNames rcFreeze rc ic rcPair icPower
    rcNamePair coordinates

#classicism_check natural_cohen_possible_not_cardinalCH
#classicism_types natural_cohen_possible_not_cardinalCH
end Classicism.MathematicalContingency
