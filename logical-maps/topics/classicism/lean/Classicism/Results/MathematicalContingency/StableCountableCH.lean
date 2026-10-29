import Classicism.Results.MathematicalContingency.StableSurjectionCH

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {κ σ τ β γ : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β] [Ty γ]

theorem stable_countableBitSetup_possible_orderTypeCH
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (limit : StrongLimit K L) (rcK : Classicism.P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity σ) (I : τ → Prop) (setup : CountableBitSetup (σ := σ) K L I)
    (rcConditions : Classicism.P.RigidComprehension (CountableBitGraph σ τ → Prop))
    (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA H R)
    (cones : ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (incompatible : ∀ o i, Endpoints H R o i →
      IncompatibleCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (rigidN : Rigid (@LowerNat σ _))
    (D : τ → Prop) (RD LI : τ → τ → Prop)
    (stable : StableIndexPresentation (@LowerNat σ _) D I RD LI)
    (rcH : □ (Classicism.P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop)))
    (rcGraph : Classicism.P.RigidComprehension (CountableBitGraph σ τ))
    (rcNames : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : Classicism.P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rcM : Classicism.P.RigidComprehension (τ → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcN : □ (Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : Classicism.P.IntensionalChoice (((σ → Prop) → Prop) → Prop)) :
    ◇ (Equinumerous (RigidPower (@LowerNat σ _)) (HartogsCarrier (@LowerNat σ _))) :=
  stableIndex_possible_orderTypeCH LowerNat D I RD LI stable rcN rcH
    (countableBitSetup_possible_surjects K L mp limit rcK hi I setup rcConditions H R C cba
      cones incompatible rigidN stable.1 stable.2.2.2.2.1 stable.2.2.2.2.2.2.1
      rcGraph rcNames rcFreeze rcM rcN ic)

#classicism_check stable_countableBitSetup_possible_orderTypeCH
#classicism_types stable_countableBitSetup_possible_orderTypeCH
end Classicism.MathematicalContingency
