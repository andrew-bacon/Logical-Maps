import Classicism.Results.MathematicalContingency.CountableCompletionCH

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

theorem natural_countable_possible_orderTypeCH
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (inaccessible : StronglyInaccessible K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity e)
    (rcConditions : Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (completion : ∀ I LI, StableHartogsPresentation (@LowerNat e _) I LI →
      CountableCompletion (σ := e) (β := β) I)
    (rigidN : Rigid (@LowerNat e _))
    (rcNatPair : P.RigidComprehension (((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcStableMap : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (closed : ∀ i, HartogsCarrier (@LowerNat e _) i →
      Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) i) (@LowerNat e _))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcCode : P.RigidComprehension
      (((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcH : □ (Classicism.P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop)))
    (rcGraph : Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop))))
    (rcNames : Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop))
    (rcM : Classicism.P.RigidComprehension ((OrdinalCarrier ((e → Prop) → Prop)) → (((e → Prop) → Prop) → Prop) → Prop))
    (rcN : □ (Classicism.P.RigidComprehension (((e → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice (((e → Prop) → Prop) → Prop)) :
    ◇ (Equinumerous (RigidPower (@LowerNat e _)) (HartogsCarrier (@LowerNat e _))) := by
  obtain ⟨I,LI,stable⟩ := natural_stable_hartogs_presentation hi rigidN (box_elim rcN)
    rcNatPair (box_elim rcH) rcPair rcStableMap
  exact hartogs_completion_possible_orderTypeCH K L mp inaccessible rcK hi I rcConditions
    (completion I LI stable) rigidN LI stable closed rcPair rcCode rcH rcGraph rcNames rcFreeze rcM rcN ic

#classicism_check natural_countable_possible_orderTypeCH
#classicism_types natural_countable_possible_orderTypeCH
end Classicism.MathematicalContingency
