import Classicism.Results.MathematicalContingency.MPInterval
import Classicism.Results.MathematicalContingency.CohenCompletionCH

/-!
The conditional negative cardinal-CH branch after applying MP.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Smallness and the completion outputs are hypotheses, not constructed here.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty γ]

theorem cohen_possible_not_cardinalCH_of_small_completion
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt γ K L) (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : CBA H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (incompatible : IncompatibleCones (CohenCondition I)
      (ConditionOrder LowerNat I ConditionBit) H R o C)
    (small : Small K L H) (member : H o) (least : ∀ b, H b → R o b)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (coordinates : ∃ J LJ QJ, CohenCoordinateBounds (@LowerNat σ _) I J LJ QJ) :
    ◇ (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) := by
  obtain ⟨P,F,hf,ho⟩ := mp_interval_zero K L mp H R hH small o member least
  exact (cohen_not_cardinalCH_of_completion hi I rcC LC H R o C hH hwC hc incompatible
    F P hf ho rigidN rcNames rcFreeze rc ic rcPair icPower rcNamePair coordinates).2

#classicism_check cohen_possible_not_cardinalCH_of_small_completion
#classicism_types cohen_possible_not_cardinalCH_of_small_completion
end Classicism.MathematicalContingency
