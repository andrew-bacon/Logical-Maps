import Classicism.Results.MathematicalContingency.NaturalPositivePrinciples

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

def NaturalNegativeRC : Prop :=
  □ (Classicism.P.RigidComprehension (κ → Prop)) ∧
  □ (P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop)) ∧
  □ (P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)) ∧
  □ (P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop)) ∧
  □ (P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop)) ∧
  □ (Classicism.P.RigidComprehension (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))))) ∧
  □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop)) ∧
  □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop))

theorem natural_negative_CH_from_principles
    (K : κ → Prop)
    (L : κ → κ → Prop)
    (mp : MPAt γ K L)
    (inaccessible : StronglyInaccessible K L)
    (hi : DraftBoxInfinity e)
    (rcs : NaturalNegativeRC (κ := κ))
    (closed1 : ∀ h, HartogsCarrier (@LowerNat e _) h → Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) h) (@LowerNat e _))
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier (@LowerNat e _)) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier (@LowerNat e _))) (HartogsOrder (HartogsCarrier (@LowerNat e _))) j) (HartogsCarrier (@LowerNat e _)))
    (completion : NaturalCohenCompletion (γ := γ))
    (rigidN : Rigid (@LowerNat e _))
    (ic : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (icPower : Classicism.P.IntensionalChoice ((((e → Prop) → Prop) → Prop) → (((e → Prop) → Prop) → Prop) → Prop))
    : (◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _)))) ∧ ◇ (¬ Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) := by
  obtain ⟨rcK,rc1,rp1,rc2,rp2,rcC,rcNames,rcFreeze,rc,rcPair,rcNamePair⟩ := rcs
  exact natural_cohen_completion_possible_not_CH K L mp inaccessible rcK hi rc1 rp1 rc2 rp2
    closed1 closed2 rcC completion rigidN rcNames rcFreeze rc ic rcPair icPower rcNamePair

#classicism_check natural_negative_CH_from_principles
#classicism_types natural_negative_CH_from_principles
end Classicism.MathematicalContingency
