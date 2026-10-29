import Classicism.Results.MathematicalContingency.CohenCoordinateValues
import Classicism.Results.MathematicalContingency.CohenCardinalCH

/-!
The negative cardinal-CH conclusion from an explicit Cohen completion.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Coordinate proposition laws, totality, functionality, proposition cones and
nonzero P are now derived. Completion, its incompatibility preservation,
interval representation, condition well-order and cardinal bounds stay explicit.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ γ : Type} [Ty σ] [Ty τ] [Ty γ]

theorem cohen_not_cardinalCH_of_completion (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : CBA H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (incompatible : IncompatibleCones (CohenCondition I)
      (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (coordinates : ∃ K LK QK, CohenCoordinateBounds (@LowerNat σ _) I K LK QK) :
    EntailmentOrder P (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) ∧
      ◇ (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) := by
  obtain ⟨cones,hnP,laws,total,functional⟩ :=
    cohenCoordinateValue_interfaces I rcC H R o C hH hc incompatible F P hf ho
  exact cohen_not_cardinalCH_of_coordinate_bounds hi I rcC LC H R o C hH.1 hwC hc
    F P hf ho rigidN rcNames rcFreeze (RelCompose C F) (CohenCoordinateValue I H R C F)
    hnP cones laws total functional rc ic rcPair icPower rcNamePair coordinates

#classicism_check cohen_not_cardinalCH_of_completion
#classicism_types cohen_not_cardinalCH_of_completion
end Classicism.MathematicalContingency
