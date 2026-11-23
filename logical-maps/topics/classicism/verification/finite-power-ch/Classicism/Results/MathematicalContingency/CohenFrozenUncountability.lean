import Classicism.Results.MathematicalContingency.CohenFrozenNames
import Classicism.Results.MathematicalContingency.CohenUncountability
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ γ : Type} [Ty σ] [Ty τ] [Ty γ]

/-- Construct the frozen intermediate collection from an uncountable coordinate subfamily. -/
theorem cohen_frozen_intermediate_uncountable (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (Cp : CohenGraph σ τ → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (hnP : P ≠ False)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) Cp P)
    (laws : CohenCoordinateLaws I Cp T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → LowerNat n → T a n p → T a n q → p = q)
    (K : τ → Prop) (sub : ∀ a, K a → I a) (large : ¬ Embeds K (@LowerNat σ _))
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)) :
    ∃ E, Rigid E ∧ E ≡ NameCarrier LowerNat K T ∧
      □ (∀ U, RepresentativeImage E U → RigidPower (@LowerNat σ _) U) ∧
      EntailmentOrder P (¬ Embeds (RepresentativeImage E) (@LowerNat σ _)) := by
  obtain ⟨E,he,hco,hlarge,hsep,hsub⟩ := cohen_frozen_subfamily_exists hi I rigidN rcNames rcC
    Cp T P hnP cones laws total functional K sub rcFreeze large
  exact ⟨E,he,hco,representativeImage_rigidPower LowerNat E he hsub,
    cohen_intermediate_uncountable (box_elim hi) I rcC LC H R o C hH hwC hc F P hf ho
      E he rigidN rc ic rcPair hsep hlarge⟩

#classicism_check cohen_frozen_intermediate_uncountable
#classicism_types cohen_frozen_intermediate_uncountable
end Classicism.MathematicalContingency
