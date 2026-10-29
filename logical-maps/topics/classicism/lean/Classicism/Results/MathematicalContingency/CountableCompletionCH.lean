import Classicism.Results.MathematicalContingency.HartogsCountableCH

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

def CountableCompletion (I : τ → Prop) : Prop :=
  ∃ (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop),
    CBA H R ∧ ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C ∧
      IncompatibleCones (CountableBitCarrier I) (CountableBitOrder I) H R o C

theorem hartogs_completion_possible_orderTypeCH
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (inaccessible : StronglyInaccessible K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity e) (I : (OrdinalCarrier ((e → Prop) → Prop)) → Prop)
    (rcConditions : Classicism.P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (completion : CountableCompletion (σ := e) (β := β) I)
    (rigidN : Rigid (@LowerNat e _))
    (LI : OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)
    (stable : StableHartogsPresentation (@LowerNat e _) I LI)
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
  obtain ⟨H,R,C,cba,cones⟩ := completion
  exact hartogs_countable_possible_orderTypeCH K L mp inaccessible rcK hi I rcConditions
    H R C cba (fun o i he => (cones o i he).1) (fun o i he => (cones o i he).2)
    rigidN LI stable closed rcPair rcCode rcH rcGraph rcNames rcFreeze rcM rcN ic

#classicism_check hartogs_completion_possible_orderTypeCH
#classicism_types hartogs_completion_possible_orderTypeCH
end Classicism.MathematicalContingency
