import Classicism.Results.MathematicalContingency.FiniteOrdinalBenchmark
import Classicism.Results.MathematicalContingency.FinitePowerSmallness

/-! Start finite represented-power towers at the native numerical carrier.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {η α β σ : Type} [Ty η] [Ty α] [Ty β] [Ty σ]

theorem powerBound_of_embeds (H : η → Prop) (A : α → Prop) (B : β → Prop)
    (embed : Embeds A B) (bound : PowerBound H B σ) : PowerBound H A σ := by
  intro Y large closed
  have hb := bound Y large closed
  exact ⟨embeds_trans A B Y embed hb.1,
    fun reverse => hb.2 (embeds_trans Y A B reverse embed)⟩

theorem lowerNat_powerBound (hp : LowerPeano e) :
    PowerBound (@Ordinal e _) (@LowerNat e _) σ :=
  powerBound_of_embeds Ordinal LowerNat Ordinal (lowerNat_embeds_ordinal hp)
    (powerBound_base Ordinal)

theorem lowerNat_small (hp : LowerPeano e) : Small (@LowerNat e _) :=
  smallAbove_of_embeds_benchmark Ordinal LowerNat (lowerNat_embeds_ordinal hp)

#classicism_check powerBound_of_embeds lowerNat_powerBound lowerNat_small
#classicism_types powerBound_of_embeds lowerNat_powerBound lowerNat_small
end Classicism.MathematicalContingency.FinitePower
