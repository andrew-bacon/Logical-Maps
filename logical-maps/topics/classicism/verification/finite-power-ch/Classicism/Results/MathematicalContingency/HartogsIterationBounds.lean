import Classicism.Results.MathematicalContingency.HartogsFinitePowerBounds

/-! Compose the two realized-Hartogs bounds at an explicit pairing interface.
The numerical specialization discharges that interface using the existing
closed-segment proof. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {η α β σ : Type} [Ty η] [Ty α] [Ty β] [Ty σ]

theorem twoRigidPowers_embeds (A : α → Prop) (B : β → Prop)
    (rc : P.RigidComprehension (β → Prop))
    (rcPower : P.RigidComprehension ((β → Prop) → Prop)) (h : Embeds A B) :
    Embeds (RigidPower (RigidPower A)) (RigidPower (RigidPower B)) :=
  rigidPower_embeds_of_embeds (RigidPower A) (RigidPower B) rcPower
    (rigidPower_embeds_of_embeds A B rc h)

theorem secondHartogs_embeds_fourRigidPowers (A : α → Prop)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (pairing : ∃ R, PairingOn (HartogsCarrier A) R)
    (rc1 : P.RigidComprehension (α → Prop))
    (rc2 : P.RigidComprehension ((α → Prop) → Prop))
    (rc3 : P.RigidComprehension (((α → Prop) → Prop) → Prop))
    (rc4 : P.RigidComprehension ((((α → Prop) → Prop) → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rcHPower : P.RigidComprehension ((OrdinalCarrier α → Prop) → Prop)) :
    Embeds (HartogsCarrier (HartogsCarrier A))
      (RigidPower (RigidPower (RigidPower (RigidPower A)))) := by
  obtain ⟨R,hR⟩ := pairing
  have first := hartogs_embeds_twoRigidPowers A Q hq rc1 rc2
  have second := hartogs_embeds_twoRigidPowers (HartogsCarrier A) R hR rcH rcHPower
  exact embeds_trans _ (RigidPower (RigidPower (HartogsCarrier A))) _ second
    (twoRigidPowers_embeds (HartogsCarrier A) (RigidPower (RigidPower A)) rc3 rc4 first)

theorem secondHartogs_powerBound (H : η → Prop) (A : α → Prop)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (pairing : ∃ R, PairingOn (HartogsCarrier A) R)
    (rc1 : P.RigidComprehension (α → Prop))
    (rc2 : P.RigidComprehension ((α → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rcHPower : P.RigidComprehension ((OrdinalCarrier α → Prop) → Prop))
    (bound : PowerBound H A σ) : PowerBound H (HartogsCarrier (HartogsCarrier A)) σ := by
  obtain ⟨R,hR⟩ := pairing
  exact hartogs_powerBound H (HartogsCarrier A) R hR rcH rcHPower
    (hartogs_powerBound H A Q hq rc1 rc2 bound)

theorem lowerNat_secondHartogs_small_of_pairing (hp : LowerPeano e)
    (pairing : ∃ R, PairingOn (HartogsCarrier (@LowerNat e _)) R)
    (rc1 : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop))
    (rcH : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcHPower : P.RigidComprehension ((OrdinalCarrier ((e → Prop) → Prop) → Prop) → Prop)) :
    Small (HartogsCarrier (HartogsCarrier (@LowerNat e _))) :=
  smallAbove_of_powerBound Ordinal _ _
    (secondHartogs_powerBound Ordinal LowerNat LowerPair (lowerPair_pairing hp)
      pairing rc1 rc2 rcH rcHPower (lowerNat_powerBound hp))
    (embeds_refl (HartogsCarrier (HartogsCarrier LowerNat)))

#classicism_check twoRigidPowers_embeds secondHartogs_embeds_fourRigidPowers
  secondHartogs_powerBound lowerNat_secondHartogs_small_of_pairing
#classicism_types twoRigidPowers_embeds secondHartogs_embeds_fourRigidPowers
  secondHartogs_powerBound lowerNat_secondHartogs_small_of_pairing
end Classicism.MathematicalContingency.FinitePower
