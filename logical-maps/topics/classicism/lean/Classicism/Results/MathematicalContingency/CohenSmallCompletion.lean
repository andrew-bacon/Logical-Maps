import Classicism.Results.MathematicalContingency.SmallnessTransfer
import Classicism.Results.MathematicalContingency.PairingAbsorption
import Classicism.Results.MathematicalContingency.CohenConditions

/-!
The Cohen completion is small when its paired condition bound is small.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The completion-to-power embedding is derived from CBA and DenseCones.
No extra RC instance at the condition-predicate type is introduced.
-/
namespace Classicism.MathematicalContingency
variable {κ σ τ γ δ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty γ] [Ty δ]

theorem cohen_completion_small (K : κ → Prop) (L : κ → κ → Prop)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (I : τ → Prop) (J : δ → Prop) (LJ : δ → δ → Prop) (QJ : δ → δ → δ → Prop)
    (rcJ : P.RigidComprehension (δ → Prop)) (hwJ : WellOrderOn J LJ) (pairing : PairingOn J QJ)
    (u v : δ) (hu : J u) (hv : J v) (hne : u ≠ v)
    (naturals : Embeds (@LowerNat σ _) J) (indices : Embeds I J) (bits : Embeds ConditionBit J)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ)
    (C : (((σ → Prop) → Prop) → τ → Prop → Prop) → γ → Prop)
    (cba : CBA H R) (member : H o) (least : ∀ b, H b → R o b)
    (cones : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (smallJ : Small K L J) : Small K L H :=
  denseCones_small K L limit rcK (CohenCondition I) (ConditionOrder LowerNat I ConditionBit)
    H R o C cba member least cones J rcJ
    (finiteCondition_bound_of_pairing LowerNat I ConditionBit J QJ rcJ LJ hwJ pairing
      u v hu hv hne naturals indices bits) smallJ

#classicism_check cohen_completion_small
#classicism_types cohen_completion_small
end Classicism.MathematicalContingency
