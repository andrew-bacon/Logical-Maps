import Classicism.Results.MathematicalContingency.RegularOpenHull
import Classicism.Results.MathematicalContingency.RigidImageCoding
import Classicism.Results.MathematicalContingency.NumericalPowerBounds
import Classicism.Results.MathematicalContingency.RigidRepresentedPower

/-! Bounds for the native rigid regular-open carrier, without a CBA size witness.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {η α β σ : Type} [Ty η] [Ty α] [Ty β] [Ty σ]

theorem roCarrier_embeds_rigidPower (Q : α → Prop) (E : α → α → Prop) :
    Embeds (ROCarrier Q E) (RigidPower Q) :=
  embeds_of_subset _ _ (fun U h => ⟨h.1,fun q hq => ((h.2 q).mp hq).1⟩)

theorem roCarrier_embeds_power_of_embeds (Q : α → Prop) (E : α → α → Prop)
    (J : β → Prop) (rc : P.RigidComprehension (β → Prop)) (bound : Embeds Q J) :
    Embeds (ROCarrier Q E) (RigidPower J) :=
  embeds_trans _ (RigidPower Q) _ (roCarrier_embeds_rigidPower Q E)
    (rigidPower_embeds_of_embeds Q J rc bound)

theorem roCarrier_powerBound (H : η → Prop) (Q : α → Prop) (E : α → α → Prop)
    (J : β → Prop) (rc : P.RigidComprehension (β → Prop))
    (bound : PowerBound H J σ) (embed : Embeds Q J) :
    PowerBound H (ROCarrier Q E) σ :=
  powerBound_of_embeds H _ (RigidPower J)
    (roCarrier_embeds_power_of_embeds Q E J rc embed)
    (powerBound_step H J (RigidPower J) bound (pow_rigidPower J rc))

theorem roCarrier_smallAbove (H : η → Prop) (Q : α → Prop) (E : α → α → Prop)
    (J : β → Prop) (rc : P.RigidComprehension (β → Prop))
    (bound : PowerBound H J (α → Prop)) (embed : Embeds Q J) :
    SmallAbove H (ROCarrier Q E) :=
  smallAbove_of_powerBound H _ _ (roCarrier_powerBound H Q E J rc bound embed)
    (embeds_refl (ROCarrier Q E))

#classicism_check roCarrier_embeds_rigidPower roCarrier_embeds_power_of_embeds
  roCarrier_powerBound roCarrier_smallAbove
#classicism_types roCarrier_embeds_rigidPower roCarrier_embeds_power_of_embeds
  roCarrier_powerBound roCarrier_smallAbove
end Classicism.MathematicalContingency.FinitePower
