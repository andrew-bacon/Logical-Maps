import Classicism.Results.MathematicalContingency.NaturalNegativeCompletion

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

def NaturalPositiveRC : Prop :=
  □ (Classicism.P.RigidComprehension (κ → Prop)) ∧
  □ (Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop)) ∧
  □ (P.RigidComprehension (((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop)) ∧
  □ (P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop)) ∧
  □ (P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)) ∧
  □ (P.RigidComprehension
      (((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)))) ∧
  □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop)) ∧
  □ (Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension ((OrdinalCarrier ((e → Prop) → Prop)) → (((e → Prop) → Prop) → Prop) → Prop)) ∧
  □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop))

theorem natural_positive_CH_from_principles
    (K : κ → Prop)
    (L : κ → κ → Prop)
    (mp : MPAt β K L)
    (inaccessible : StronglyInaccessible K L)
    (hi : DraftBoxInfinity e)
    (rcs : NaturalPositiveRC (κ := κ))
    (completion : ∀ I LI, StableHartogsPresentation (@LowerNat e _) I LI →
      CountableCompletion (σ := e) (β := β) I)
    (rigidN : Rigid (@LowerNat e _))
    (closed : ∀ i, HartogsCarrier (@LowerNat e _) i →
      Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) i) (@LowerNat e _))
    (ic : Classicism.P.IntensionalChoice (((e → Prop) → Prop) → Prop))
    : (◇ (Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _)))) ∧ ◇ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) := by
  obtain ⟨rcK,rcConditions,rcNatPair,rcStableMap,rcPair,rcCode,rcH,rcGraph,rcNames,rcFreeze,rcM,rcN⟩ := rcs
  have hp := natural_countable_possible_orderTypeCH K L mp inaccessible (box_elim rcK) hi
    (box_elim rcConditions) completion rigidN (box_elim rcNatPair) (box_elim rcStableMap)
    closed (box_elim rcPair) (box_elim rcCode) rcH (box_elim rcGraph) (box_elim rcNames)
    (box_elim rcFreeze) (box_elim rcM) rcN ic
  have hc := dia_mono _ _
    (modal_K _ _ (nec% (fun
      (hrc : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
      (he : Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) =>
      cardinalCH_of_equinumerous_hartogs LowerNat (RigidPower LowerNat) hrc he)) rcH) hp
  exact ⟨hp,hc⟩

#classicism_check natural_positive_CH_from_principles
#classicism_types natural_positive_CH_from_principles
end Classicism.MathematicalContingency
