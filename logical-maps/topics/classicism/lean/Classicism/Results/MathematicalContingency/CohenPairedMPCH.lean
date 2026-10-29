import Classicism.Results.MathematicalContingency.ConditionWellOrder
import Classicism.Results.MathematicalContingency.CohenMPCH

/-!
The Cohen-MP conclusion with its condition well-order derived from a paired bound.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The paired bound J, the inaccessible-bound carrier K, and the intermediate
coordinate carrier are separate inputs. Completion smallness remains explicit.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ γ δ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty γ] [Ty δ]

theorem cohen_possible_not_cardinalCH_of_paired_bound
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt γ K L) (hi : DraftBoxInfinity σ) (I : τ → Prop)
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
    (small : Small K L H) (member : H o) (least : ∀ b, H b → R o b)
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
  obtain ⟨LC,hwC⟩ := cohenCondition_wellOrder_of_pairing I J QJ rcJ LJ hwJ pairing
    u v hu hv hne naturals indices bits
  exact cohen_possible_not_cardinalCH_of_small_completion K L mp hi I rcC LC
    H R o C hH hwC hc incompatible small member least rigidN rcNames rcFreeze
    rc ic rcPair icPower rcNamePair coordinates

#classicism_check cohen_possible_not_cardinalCH_of_paired_bound
#classicism_types cohen_possible_not_cardinalCH_of_paired_bound
end Classicism.MathematicalContingency
