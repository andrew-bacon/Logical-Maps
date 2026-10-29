import Classicism.Results.MathematicalContingency.NameCardinalTransport
import Classicism.Results.MathematicalContingency.CohenFrozenNames
import Classicism.Results.MathematicalContingency.CohenPowerObstruction
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ γ : Type} [Ty σ] [Ty τ] [Ty γ]

/-- Instantiate the second modal obstruction with actual Cohen name families and coordinate bounds. -/
theorem cohen_frozen_rigidPower_no_injection (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (Cp : CohenGraph σ τ → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (hnP : P ≠ False)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) Cp P)
    (laws : CohenCoordinateLaws I Cp T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → LowerNat n → T a n p → T a n q → p = q)
    (K : τ → Prop) (sub : ∀ a, K a → I a)
    (LK : τ → τ → Prop) (hwK : WellOrderOn K LK)
    (QK : τ → τ → τ → Prop) (hqK : PairingOn K QK)
    (natK : Embeds (@LowerNat σ _) K) (gap : ¬ Embeds I K)
    (E : ((((σ → Prop) → Prop) → Prop) → Prop)) (he : Rigid E)
    (hco : E ≡ NameCarrier LowerNat K T)
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)) :
    EntailmentOrder P (¬ Embeds (RigidPower (@LowerNat σ _)) (RepresentativeImage E)) := by
  have hI := cohen_names_bijects hi I rigidN rcNames rcC Cp T P hnP cones laws total functional
  have hK := bijects_target_coext K (NameCarrier LowerNat K T) E (IndexedName LowerNat K T)
    (indexedName_subfamily_bijects LowerNat I K T sub hI) hco
  exact cohen_rigidPower_no_injection (box_elim hi) I rcC LC H R o C hH hwC hc F P hf ho
    LowerNat (NameCarrier LowerNat I T) E (ImageOrder (IndexedName LowerNat K T) LK)
    (bijects_image_wellOrder K E (IndexedName LowerNat K T) LK hK hwK) he rc ic rcPair
    (fun X hx => modal_K _ _ (nec% (fun (h : ∀ n, X n → LowerNat n) (_ : P) => h))
      (nameCarrier_subsets LowerNat I T X hx))
    (cohen_subfamily_separation (box_elim hi) I I (fun _ h => h) rigidN rcC Cp T P cones laws total)
    (nameCarrier_product_gap LowerNat I K T E LowerNat hI hK QK hqK natK gap)

#classicism_check cohen_frozen_rigidPower_no_injection
#classicism_types cohen_frozen_rigidPower_no_injection
end Classicism.MathematicalContingency
