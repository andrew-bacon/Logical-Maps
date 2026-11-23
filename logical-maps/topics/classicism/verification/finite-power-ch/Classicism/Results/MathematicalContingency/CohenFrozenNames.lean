import Classicism.Results.MathematicalContingency.FrozenNameCarriers
import Classicism.Results.MathematicalContingency.CohenSeparation
import Classicism.Results.MathematicalContingency.RepresentativeFibres
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ : Type} [Ty σ] [Ty τ]

/-- Distinct names from any current coordinate subfamily are separated under P. -/
theorem cohen_subfamily_separation (hp : LowerPeano σ) (I K : τ → Prop)
    (sub : ∀ a, K a → I a) (rigidN : Rigid (@LowerNat σ _))
    (rc : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → τ → Prop → Prop)))
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) C P)
    (laws : CohenCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (X Y : ((σ → Prop) → Prop) → Prop)
    (hx : NameCarrier LowerNat K T X) (hy : NameCarrier LowerNat K T Y) (hn : X ≠ Y) :
    EntailmentOrder P (¬ (X ≡ Y)) :=
  nameCarrier_separation LowerNat K T P rigidN (fun a n ha hn => total a n (sub a ha) hn)
    (fun a b X Y ha hb hn => cohen_names_separate hp I rc C T P cones laws total a b X Y
      ⟨sub a ha.1,ha.2⟩ ⟨sub b hb.1,hb.2⟩ hn) X Y hx hy hn

/-- Freeze an actual Cohen name subfamily, retaining its current uncountability and modal laws. -/
theorem cohen_frozen_subfamily_exists (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcConditions : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → τ → Prop → Prop))
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → Prop → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (P : Prop) (hnP : P ≠ False)
    (cones : PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) C P)
    (laws : CohenCoordinateLaws I C T)
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → LowerNat n → T a n p → T a n q → p = q)
    (K : τ → Prop) (sub : ∀ a, K a → I a)
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (large : ¬ Embeds K (@LowerNat σ _)) :
    ∃ E, Rigid E ∧ E ≡ NameCarrier LowerNat K T ∧ ¬ Embeds E (@LowerNat σ _) ∧
      (∀ X Y, E X → E Y → X ≠ Y → EntailmentOrder P (¬ (X ≡ Y))) ∧
      (∀ X, E X → □ (∀ n, X n → LowerNat n)) := by
  obtain ⟨E,he,hco⟩ := rigid_representative_exists rcFreeze (NameCarrier LowerNat K T)
  have bij := indexedName_subfamily_bijects LowerNat I K T sub
    (cohen_names_bijects hi I rigidN rcNames rcConditions C T P hnP cones laws total functional)
  refine ⟨E,he,hco,frozenNameCarrier_not_embeds LowerNat K T E LowerNat bij hco large,?_,?_⟩
  · intro X Y hx hy hn
    exact cohen_subfamily_separation (box_elim hi) I K sub rigidN rcConditions C T P
      cones laws total X Y ((hco X).mp hx) ((hco Y).mp hy) hn
  · intro X hx
    exact nameCarrier_subsets LowerNat K T X ((hco X).mp hx)

#classicism_check cohen_subfamily_separation cohen_frozen_subfamily_exists
#classicism_types cohen_subfamily_separation cohen_frozen_subfamily_exists
end Classicism.MathematicalContingency
