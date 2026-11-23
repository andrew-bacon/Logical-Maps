import Classicism.Results.MathematicalContingency.CohenFrozenPower
import Classicism.Results.MathematicalContingency.CohenFrozenUncountability
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ γ : Type} [Ty σ] [Ty τ] [Ty γ]

/-- Both modal cardinal obstructions hold for the same frozen Cohen name collection. -/
theorem cohen_frozen_intermediate_obstructions (hi : DraftBoxInfinity σ) (I : τ → Prop)
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
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (LK : τ → τ → Prop) (hwK : WellOrderOn K LK)
    (QK : τ → τ → τ → Prop) (hqK : PairingOn K QK)
    (natK : Embeds (@LowerNat σ _) K) (gap : ¬ Embeds I K)
    (icPower : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)) :
    ∃ E, Rigid E ∧ E ≡ NameCarrier LowerNat K T ∧
      □ (∀ U, RepresentativeImage E U → RigidPower (@LowerNat σ _) U) ∧
      EntailmentOrder P (¬ Embeds (RepresentativeImage E) (@LowerNat σ _) ∧
        ¬ Embeds (RigidPower (@LowerNat σ _)) (RepresentativeImage E)) := by
  obtain ⟨E,he,hco,hsub,hunc⟩ := cohen_frozen_intermediate_uncountable hi I rcC LC H R o C
    hH hwC hc F P hf ho rigidN rcNames rcFreeze Cp T hnP cones laws total functional K sub large rc ic rcPair
  have hpower := cohen_frozen_rigidPower_no_injection hi I rcC LC H R o C hH hwC hc F P hf ho
    rigidN rcNames Cp T hnP cones laws total functional K sub LK hwK QK hqK natK gap E he hco rc icPower rcNamePair
  exact ⟨E,he,hco,hsub,modal_K _ _ (modal_K _ _
    (nec% (fun (h : P → ¬ Embeds (RepresentativeImage E) (@LowerNat σ _))
      (k : P → ¬ Embeds (RigidPower (@LowerNat σ _)) (RepresentativeImage E)) (hp : P) =>
        ⟨h hp,k hp⟩)) hunc) hpower⟩

#classicism_check cohen_frozen_intermediate_obstructions
#classicism_types cohen_frozen_intermediate_obstructions
end Classicism.MathematicalContingency
