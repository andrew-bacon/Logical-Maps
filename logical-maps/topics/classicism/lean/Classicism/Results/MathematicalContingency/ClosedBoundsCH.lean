import Classicism.Results.MathematicalContingency.NaturalClosedBounds
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ : Type} [Ty κ]

theorem natural_CH_contingency_closedBounds
    (K : κ → Prop) (L : κ → κ → Prop)
    (positiveMP : MPAt (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop) K L)
    (negativeMP : MPAt (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) K L)
    (inaccessible : StronglyInaccessible K L) (hi : DraftBoxInfinity e)
    (positiveRC : NaturalPositiveRC (κ := κ))
    (negativeRC : NaturalNegativeRC (κ := κ))
    (completionRC : □ (P.RigidComprehension
      (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)))
    (choice : NaturalCHChoice) (rigidN : Rigid (@LowerNat e _))
    : NaturalCHContingency :=
  natural_CH_contingency_regularOpen K L positiveMP negativeMP inaccessible hi positiveRC negativeRC
    completionRC choice rigidN (natural_hartogs_closedSegments (lowerPeano_of_box hi)
      (box_elim negativeRC.2.1) (box_elim negativeRC.2.2.1))

#classicism_check natural_CH_contingency_closedBounds
#classicism_types natural_CH_contingency_closedBounds
end Classicism.MathematicalContingency
