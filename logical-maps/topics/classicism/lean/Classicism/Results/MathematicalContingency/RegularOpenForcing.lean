import Classicism.Results.MathematicalContingency.RegularOpenBottom
import Classicism.Results.MathematicalContingency.NaturalCHNonnecessity
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ : Type} [Ty σ] [Ty τ]

theorem countable_regularOpen_completion (I : τ → Prop)
    (rc : P.RigidComprehension (CountableBitGraph σ τ → Prop)) :
    CountableCompletion (σ := σ) (β := CountableBitGraph σ τ → Prop) I := by
  have hp : PartialOrderOn (@CountableBitCarrier σ τ _ _ I) (CountableBitOrder I) :=
    countableConditionOrder_partialOrder LowerNat LowerNat I ConditionBit
  exact regularOpen_exists (CountableBitCarrier I) (CountableBitOrder I) hp rc

theorem natural_cohen_regularOpen_completion
    (rc : P.RigidComprehension (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)) :
    NaturalCohenCompletion (γ := CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) := by
  let Q := @CohenCondition e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) _ _
    (HartogsCarrier (HartogsCarrier (@LowerNat e _)))
  let E := ConditionOrder (@LowerNat e _) (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ConditionBit
  have hp : PartialOrderOn Q E := cohenCondition_partialOrder (HartogsCarrier (HartogsCarrier (@LowerNat e _)))
  exact regularOpen_exists_bottom Q E hp rc

theorem natural_regularOpen_completions
    (positiveRC : P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (negativeRC : P.RigidComprehension (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)) :
    NaturalCHCompletions
      (β := CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop)
      (γ := CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) :=
  ⟨fun I _ _ => countable_regularOpen_completion I positiveRC,
    natural_cohen_regularOpen_completion negativeRC⟩

#classicism_check countable_regularOpen_completion natural_cohen_regularOpen_completion natural_regularOpen_completions
#classicism_types countable_regularOpen_completion natural_cohen_regularOpen_completion natural_regularOpen_completions
end Classicism.MathematicalContingency
