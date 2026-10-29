import Classicism.Results.MathematicalContingency.CohenSmallCompletion
import Classicism.Results.MathematicalContingency.CohenPairedMPCH

/-!
The Cohen-MP conclusion with completion smallness derived from a small paired bound.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The CBA, dense and incompatible cones, coordinate bounds and displayed RC/IC
inputs remain explicit. No completion-to-power embedding is assumed.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ γ δ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty γ] [Ty δ]

theorem cohen_possible_not_cardinalCH_of_small_paired_bound
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt γ K L)
    (limit : StrongLimit K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (J : δ → Prop) (LJ : δ → δ → Prop) (QJ : δ → δ → δ → Prop)
    (rcJ : Classicism.P.RigidComprehension (δ → Prop))
    (hwJ : WellOrderOn J LJ) (pairing : PairingOn J QJ)
    (u v : δ) (hu : J u) (hv : J v) (hne : u ≠ v)
    (naturals : Embeds (@LowerNat σ _) J) (indices : Embeds I J)
    (bits : Embeds ConditionBit J)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : CBA H R)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (incompatible : IncompatibleCones (CohenCondition I)
      (ConditionOrder LowerNat I ConditionBit) H R o C)
    (smallJ : Small K L J) (member : H o) (least : ∀ b, H b → R o b)
    (rigidN : Rigid (@LowerNat σ _))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rc : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((σ → Prop) → Prop) → Prop) → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcNamePair : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (coordinates : ∃ I₁ L₁ Q₁, CohenCoordinateBounds (@LowerNat σ _) I I₁ L₁ Q₁) :
    ◇ (¬ CardinalCH (@LowerNat σ _) (RigidPower (@LowerNat σ _))) := by
  have smallH := cohen_completion_small K L limit rcK I J LJ QJ rcJ hwJ pairing
    u v hu hv hne naturals indices bits H R o C hH member least hc smallJ
  exact cohen_possible_not_cardinalCH_of_paired_bound K L mp hi I rcC J LJ QJ rcJ hwJ pairing
    u v hu hv hne naturals indices bits H R o C hH hc incompatible smallH member least
    rigidN rcNames rcFreeze rc ic rcPair icPower rcNamePair coordinates

#classicism_check cohen_possible_not_cardinalCH_of_small_paired_bound
#classicism_types cohen_possible_not_cardinalCH_of_small_paired_bound
end Classicism.MathematicalContingency
