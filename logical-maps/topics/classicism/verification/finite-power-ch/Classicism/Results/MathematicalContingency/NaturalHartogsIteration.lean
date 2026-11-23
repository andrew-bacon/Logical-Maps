import Classicism.Results.MathematicalContingency.HartogsIterationBounds
import Classicism.Results.MathematicalContingency.HartogsClosedBounds
import Classicism.Results.MathematicalContingency.NaturalWellOrder

/-! Discharge the pairing interface using the historically certified
closed-segment route, not the historical pending direct pairing certificate.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {σ : Type} [Ty σ]

theorem lowerNat_hartogs_pairing (hp : LowerPeano σ)
    (rcH : P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((σ → Prop) → Prop) → OrdinalCarrier ((σ → Prop) → Prop) → Prop)) :
    ∃ R, PairingOn (HartogsCarrier (@LowerNat σ _)) R :=
  (hartogs_pairing_and_two LowerNat LowerLT (lowerNat_wellOrder hp)
    ⟨LowerPair,lowerPair_pairing hp⟩
    ⟨AtLeastZero σ,SucCard (AtLeastZero σ),lowerNat_zero,
      lowerNat_suc _ lowerNat_zero,lowerNat_ne_suc_self hp _ lowerNat_zero⟩ rcH rcPair).1

theorem lowerNat_secondHartogs_powerBound (hp : LowerPeano e)
    (rc1 : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcHPower : P.RigidComprehension ((OrdinalCarrier ((e → Prop) → Prop) → Prop) → Prop)) :
    PowerBound (@Ordinal e _) (HartogsCarrier (HartogsCarrier (@LowerNat e _))) σ :=
  secondHartogs_powerBound Ordinal LowerNat LowerPair (lowerPair_pairing hp)
    (lowerNat_hartogs_pairing hp rcH rcPair) rc1 rc2 rcH rcHPower (lowerNat_powerBound hp)

theorem lowerNat_secondHartogs_small (hp : LowerPeano e)
    (rc1 : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcHPower : P.RigidComprehension ((OrdinalCarrier ((e → Prop) → Prop) → Prop) → Prop)) :
    Small (HartogsCarrier (HartogsCarrier (@LowerNat e _))) :=
  lowerNat_secondHartogs_small_of_pairing hp (lowerNat_hartogs_pairing hp rcH rcPair)
    rc1 rc2 rcH rcHPower

theorem lowerNat_secondHartogs_embeds_fourRigidPowers (hp : LowerPeano σ)
    (rc1 : P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rc3 : P.RigidComprehension (((((σ → Prop) → Prop) → Prop) → Prop) → Prop))
    (rc4 : P.RigidComprehension ((((((σ → Prop) → Prop) → Prop) → Prop) → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((σ → Prop) → Prop) → OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rcHPower : P.RigidComprehension ((OrdinalCarrier ((σ → Prop) → Prop) → Prop) → Prop)) :
    Embeds (HartogsCarrier (HartogsCarrier (@LowerNat σ _)))
      (RigidPower (RigidPower (RigidPower (RigidPower (@LowerNat σ _))))) :=
  secondHartogs_embeds_fourRigidPowers LowerNat LowerPair (lowerPair_pairing hp)
    (lowerNat_hartogs_pairing hp rcH rcPair) rc1 rc2 rc3 rc4 rcH rcHPower

#classicism_check lowerNat_hartogs_pairing lowerNat_secondHartogs_powerBound
  lowerNat_secondHartogs_small lowerNat_secondHartogs_embeds_fourRigidPowers
#classicism_types lowerNat_hartogs_pairing lowerNat_secondHartogs_powerBound
  lowerNat_secondHartogs_small lowerNat_secondHartogs_embeds_fourRigidPowers
end Classicism.MathematicalContingency.FinitePower
