import Classicism.Results.MathematicalContingency.CountableBitMP
import Classicism.Results.MathematicalContingency.NoNewRigidSubsets

namespace Classicism.MathematicalContingency
variable {κ σ τ β : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β]

theorem countableBitSetup_mp_preserves
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (hi : DraftBoxInfinity σ) (I : τ → Prop) (setup : CountableBitSetup (σ := σ) K L I)
    (rcConditions : P.RigidComprehension (CountableBitGraph σ τ → Prop))
    (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA H R)
    (cones : ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C)
    (rigidN : Rigid (@LowerNat σ _))
    (rcN : P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (rcFreeze : P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (ic : P.IntensionalChoice (((σ → Prop) → Prop) → Prop)) :
    ∃ (P : Prop) (F : β → Prop → Prop) (o i : β)
      (R₀ : (((σ → Prop) → Prop) → Prop) → Prop),
      Endpoints H R o i ∧ OrderIso F H R (Below P) EntailmentOrder ∧ F o False ∧ P ≠ False ∧
      Rigid R₀ ∧ (∀ U, RigidPower LowerNat U ↔ R₀ U) ∧
      EntailmentOrder P (∀ U, RigidPower LowerNat U ↔ R₀ U) := by
  obtain ⟨P,F,o,i,he,hF,hzero,hn,dec⟩ := countableBitSetup_mp_local K L mp limit rcK
    (lowerPeano_of_box hi) I setup rcConditions H R C cba cones
  obtain ⟨R₀,hr,co⟩ := rcFreeze (RigidPower (@LowerNat σ _))
  exact ⟨P,F,o,i,R₀,he,hF,hzero,hn,hr,co,
    localDecisions_preserves_power LowerNat R₀ P rigidN (lowerNat_nd hi) hr co rcN ic dec⟩

#classicism_check countableBitSetup_mp_preserves
#classicism_types countableBitSetup_mp_preserves
end Classicism.MathematicalContingency
