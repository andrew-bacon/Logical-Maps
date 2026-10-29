import Classicism.Results.MathematicalContingency.RCBooleanCompleteness
import Classicism.Results.MathematicalContingency.UnboxedRCRigidity
import Classicism.Results.MathematicalContingency.ClosedBoundsCH

/-! Discharges the natural-number rigidity premise of the final CH theorem
through Goodsell's countable-completeness argument. The RC instance used is
already the tenth conjunct of NaturalPositiveRC (rcFreeze).
OpenAI Codex, prompted by Andrew Bacon, 28 October 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
variable {κ : Type} [Ty κ]

theorem naturalPositiveRC_box_countable (rcs : NaturalPositiveRC (κ := κ)) :
    □ (LowerCountableBooleanCompleteAt e (((e → Prop) → Prop) → Prop)) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,rcFreeze,_,_⟩ := rcs
  exact box_countableBooleanCompleteOver_of_box_rc LowerNat rcFreeze

theorem naturalPositiveRC_lowerNat_rigid (rcs : NaturalPositiveRC (κ := κ)) :
    Rigid (@LowerNat e _) :=
  lowerNat_rigid_of_box_countable (naturalPositiveRC_box_countable rcs)

/-- Both CH formulations are contingent, with no separate rigidN premise. -/
theorem natural_CH_contingency_from_principles
    (K : κ → Prop) (L : κ → κ → Prop)
    (positiveMP : MPAt (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop) K L)
    (negativeMP : MPAt (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) K L)
    (inaccessible : StronglyInaccessible K L) (hi : DraftBoxInfinity e)
    (positiveRC : NaturalPositiveRC (κ := κ))
    (negativeRC : NaturalNegativeRC (κ := κ))
    (completionRC : □ (P.RigidComprehension
      (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)))
    (choice : NaturalCHChoice) : NaturalCHContingency :=
  natural_CH_contingency_closedBounds K L positiveMP negativeMP inaccessible hi
    positiveRC negativeRC completionRC choice (naturalPositiveRC_lowerNat_rigid positiveRC)

#classicism_check naturalPositiveRC_box_countable naturalPositiveRC_lowerNat_rigid
  natural_CH_contingency_from_principles
#classicism_types naturalPositiveRC_box_countable naturalPositiveRC_lowerNat_rigid
  natural_CH_contingency_from_principles
end Classicism.MathematicalContingency
