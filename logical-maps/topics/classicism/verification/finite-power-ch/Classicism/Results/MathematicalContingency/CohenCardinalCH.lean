import Classicism.Results.MathematicalContingency.CardinalCH
import Classicism.Results.MathematicalContingency.CohenFrozenObstructions
import Classicism.Results.MathematicalContingency.HartogsCoordinates

/-!
Connect existential coordinate bounds to the combined Cohen obstruction.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Rigidity of N, the condition well-order, completion/interval realization and
coordinate proposition laws remain displayed inputs. No positive N-to-name
embedding or rigid/necessarily distinct coordinate carrier is assumed.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ γ : Type} [Ty σ] [Ty τ] [Ty γ]

theorem cohen_not_cardinalCH_of_coordinate_bounds (hi : DraftBoxInfinity σ) (I : τ → Prop)
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
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (coordinates : ∃ K LK QK, CohenCoordinateBounds (@LowerNat σ _) I K LK QK) :
    EntailmentOrder P (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) ∧
      ◇ (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) := by
  obtain ⟨K,LK,QK,sub,hwK,hqK,natK,large,gap⟩ := coordinates
  obtain ⟨E,_,_,hsub,hobs⟩ := cohen_frozen_intermediate_obstructions hi I rcC LC H R o C
    hH hwC hc F P hf ho rigidN rcNames rcFreeze Cp T hnP cones laws total functional
    K sub large rc ic rcPair LK hwK QK hqK natK gap icPower rcNamePair
  have h := entailment_not_cardinalCH_of_obstructions LowerNat (RigidPower LowerNat)
    (RepresentativeImage E) P hsub hobs
  exact ⟨h,dia_mono P (¬ CardinalCH LowerNat (RigidPower LowerNat)) h hnP⟩

#classicism_check cohen_not_cardinalCH_of_coordinate_bounds
#classicism_types cohen_not_cardinalCH_of_coordinate_bounds
end Classicism.MathematicalContingency
