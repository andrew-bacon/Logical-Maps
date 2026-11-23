import Classicism.Results.MathematicalContingency.HartogsPowerCodes
import Classicism.Results.MathematicalContingency.NumericalPowerBounds
import Classicism.Results.MathematicalContingency.RigidRepresentedPower

/-! Realized Hartogs codes join the represented-power smallness argument.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {η α σ : Type} [Ty η] [Ty α] [Ty σ]

theorem hartogs_powerBound (H : η → Prop) (A : α → Prop)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (rc : P.RigidComprehension (α → Prop))
    (rcPower : P.RigidComprehension ((α → Prop) → Prop))
    (bound : PowerBound H A σ) : PowerBound H (HartogsCarrier A) σ :=
  powerBound_of_embeds H (HartogsCarrier A) (RigidPower (RigidPower A))
    (hartogs_embeds_twoRigidPowers A Q hq rc rcPower)
    (powerBound_step H (RigidPower A) (RigidPower (RigidPower A))
      (powerBound_step H A (RigidPower A) bound (pow_rigidPower A rc))
      (pow_rigidPower (RigidPower A) rcPower))

theorem lowerNat_hartogs_embeds_twoRigidPowers (hp : LowerPeano σ)
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (rcPower : P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop)) :
    Embeds (HartogsCarrier (@LowerNat σ _)) (RigidPower (RigidPower (@LowerNat σ _))) :=
  hartogs_embeds_twoRigidPowers LowerNat LowerPair (lowerPair_pairing hp) rc rcPower

theorem lowerNat_hartogs_powerBound (hp : LowerPeano e)
    (rc : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rcPower : P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop)) :
    PowerBound (@Ordinal e _) (HartogsCarrier (@LowerNat e _)) σ :=
  hartogs_powerBound Ordinal LowerNat LowerPair (lowerPair_pairing hp) rc rcPower
    (lowerNat_powerBound hp)

theorem lowerNat_hartogs_small (hp : LowerPeano e)
    (rc : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rcPower : P.RigidComprehension ((((e → Prop) → Prop) → Prop) → Prop)) :
    Small (HartogsCarrier (@LowerNat e _)) :=
  smallAbove_of_powerBound Ordinal (HartogsCarrier LowerNat) (HartogsCarrier LowerNat)
    (lowerNat_hartogs_powerBound hp rc rcPower) (embeds_refl (HartogsCarrier LowerNat))

#classicism_check hartogs_powerBound lowerNat_hartogs_embeds_twoRigidPowers
  lowerNat_hartogs_powerBound lowerNat_hartogs_small
#classicism_types hartogs_powerBound lowerNat_hartogs_embeds_twoRigidPowers
  lowerNat_hartogs_powerBound lowerNat_hartogs_small
end Classicism.MathematicalContingency.FinitePower
