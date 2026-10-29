import Classicism.Results.MathematicalContingency.RegularOpenForcing
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ : Type} [Ty κ]

/-- The completion obligation is discharged. Only natural rigidity and the
original Hartogs closed-segment bounds remain as mathematical deferrals. -/
theorem natural_CH_contingency_regularOpen
    (K : κ → Prop) (L : κ → κ → Prop)
    (positiveMP : MPAt (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop) K L)
    (negativeMP : MPAt (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) K L)
    (inaccessible : StronglyInaccessible K L) (hi : DraftBoxInfinity e)
    (positiveRC : NaturalPositiveRC (κ := κ))
    (negativeRC : NaturalNegativeRC (κ := κ))
    (completionRC : □ (P.RigidComprehension
      (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)))
    (choice : NaturalCHChoice) (rigidN : Rigid (@LowerNat e _))
    (closed : NaturalCHClosedSegments) : NaturalCHContingency :=
  natural_CH_contingency K L positiveMP negativeMP inaccessible hi positiveRC negativeRC
    choice rigidN closed (natural_regularOpen_completions (box_elim positiveRC.2.1) (box_elim completionRC))

#classicism_check natural_CH_contingency_regularOpen
#classicism_types natural_CH_contingency_regularOpen
end Classicism.MathematicalContingency
