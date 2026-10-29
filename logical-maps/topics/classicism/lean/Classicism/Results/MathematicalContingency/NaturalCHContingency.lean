import Classicism.Results.MathematicalContingency.NaturalNegativePrinciples

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

/-- The two original closed-segment bounds, at N and H(N). -/
def NaturalCHClosedSegments : Prop :=
  (∀ h, HartogsCarrier (@LowerNat e _) h → Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) h) (@LowerNat e _)) ∧
  (∀ j, HartogsCarrier (HartogsCarrier (@LowerNat e _)) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier (@LowerNat e _))) (HartogsOrder (HartogsCarrier (@LowerNat e _))) j) (HartogsCarrier (@LowerNat e _)))

/-- Only finite instances of the original unboxed intensional-choice scheme. -/
def NaturalCHChoice : Prop :=
  Classicism.P.IntensionalChoice (((e → Prop) → Prop) → Prop) ∧
  Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop) ∧
  Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → (((e → Prop) → Prop) → Prop) → Prop)

/-- The regular-open outputs required by the two forcing constructions. -/
def NaturalCHCompletions : Prop :=
  (∀ I LI, StableHartogsPresentation (@LowerNat e _) I LI →
      CountableCompletion (σ := e) (β := β) I) ∧ NaturalCohenCompletion (γ := γ)

/-- Both the order-type and the subset-cardinality formulations are contingent. -/
def NaturalCHContingency : Prop :=
  ((◇ (Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _)))) ∧ ◇ (¬ Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _)))) ∧
  ((◇ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _)))) ∧ ◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))))

theorem natural_CH_contingency
    (K : κ → Prop) (L : κ → κ → Prop)
    (positiveMP : MPAt β K L) (negativeMP : MPAt γ K L)
    (inaccessible : StronglyInaccessible K L) (hi : DraftBoxInfinity e)
    (positiveRC : NaturalPositiveRC (κ := κ))
    (negativeRC : NaturalNegativeRC (κ := κ))
    (choice : NaturalCHChoice)
    (rigidN : Rigid (@LowerNat e _))
    (closed : NaturalCHClosedSegments)
    (completions : NaturalCHCompletions (β := β) (γ := γ)) : NaturalCHContingency := by
  obtain ⟨hp,hpc⟩ := natural_positive_CH_from_principles K L positiveMP inaccessible hi
    positiveRC completions.1 rigidN closed.1 choice.1
  obtain ⟨hnc,hn⟩ := natural_negative_CH_from_principles K L negativeMP inaccessible hi
    negativeRC closed.1 closed.2 completions.2 rigidN choice.2.1 choice.2.2
  exact ⟨⟨hp,hn⟩,⟨hpc,hnc⟩⟩

#classicism_check natural_CH_contingency
#classicism_types natural_CH_contingency
end Classicism.MathematicalContingency
