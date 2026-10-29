import Classicism.Results.MathematicalContingency.StableCountableCH

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

theorem hartogs_countable_possible_orderTypeCH
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (inaccessible : StronglyInaccessible K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity e) (I : (OrdinalCarrier ((e → Prop) → Prop)) → Prop)
    (rcConditions : Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → β → Prop)
    (cba : CBA H R)
    (cones : ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (incompatible : ∀ o i, Endpoints H R o i →
      IncompatibleCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (rigidN : Rigid (@LowerNat e _))
    (LI : OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)
    (stable : StableHartogsPresentation (@LowerNat e _) I LI)
    (closed : ∀ i, HartogsCarrier (@LowerNat e _) i →
      Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) i) (@LowerNat e _))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcCode : P.RigidComprehension
      (((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcH : □ (Classicism.P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop)))
    (rcGraph : Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop))))
    (rcNames : Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop))
    (rcM : Classicism.P.RigidComprehension ((OrdinalCarrier ((e → Prop) → Prop)) → (((e → Prop) → Prop) → Prop) → Prop))
    (rcN : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice (((e → Prop) → Prop) → Prop)) :
    ◇ (Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) := by
  have setup := stable_hartogs_countableBitSetup_of_closedSegments K L inaccessible
    (lowerPeano_of_box hi) rcK (box_elim rcN) I LI stable closed rcPair (box_elim rcH) rcCode rcGraph
  exact stable_countableBitSetup_possible_orderTypeCH K L mp inaccessible.2.2.2 rcK hi I setup
    rcConditions H R C cba cones incompatible rigidN (HartogsCarrier LowerNat)
    (HartogsOrder LowerNat) LI stable rcH rcGraph rcNames rcFreeze rcM rcN ic

#classicism_check hartogs_countable_possible_orderTypeCH
#classicism_types hartogs_countable_possible_orderTypeCH
end Classicism.MathematicalContingency
