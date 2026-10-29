import Classicism.Results.MathematicalContingency.NaturalCHContingency

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

theorem contingency_not_necessary (p : Prop) :
    (◇ p ∧ ◇ (¬ p)) ↔ (¬ □ p ∧ ¬ □ (¬ p)) := by
  constructor
  · intro h
    exact ⟨(dia_not_eq p).mp h.2,(dia_eq_not_box_not p).mp h.1⟩
  · intro h
    exact ⟨(dia_eq_not_box_not p).mpr h.2,(dia_not_eq p).mpr h.1⟩

theorem natural_CH_nonnecessity
    (K : κ → Prop) (L : κ → κ → Prop)
    (positiveMP : MPAt β K L) (negativeMP : MPAt γ K L)
    (inaccessible : StronglyInaccessible K L) (hi : DraftBoxInfinity e)
    (positiveRC : NaturalPositiveRC (κ := κ))
    (negativeRC : NaturalNegativeRC (κ := κ))
    (choice : NaturalCHChoice)
    (rigidN : Rigid (@LowerNat e _))
    (closed : NaturalCHClosedSegments)
    (completions : NaturalCHCompletions (β := β) (γ := γ)) :
    (¬ □ (Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) ∧ ¬ □ (¬ Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _)))) ∧
    (¬ □ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) ∧ ¬ □ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _)))) := by
  have h := natural_CH_contingency K L positiveMP negativeMP inaccessible hi
    positiveRC negativeRC choice rigidN closed completions
  exact ⟨(contingency_not_necessary _).mp h.1,(contingency_not_necessary _).mp h.2⟩

#classicism_check contingency_not_necessary natural_CH_nonnecessity
#classicism_types contingency_not_necessary natural_CH_nonnecessity
end Classicism.MathematicalContingency
