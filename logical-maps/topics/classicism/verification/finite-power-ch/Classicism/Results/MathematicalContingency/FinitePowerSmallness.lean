import Classicism.Results.MathematicalContingency.RepresentedPower
import Classicism.Results.MathematicalContingency.InductiveOrdinals

/-! Finite-Power CH Strategy: finite tower rules at arbitrary admitted types.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
These rules do not require choice, comparability, regularity or well-orderability.
-/
namespace Classicism.MathematicalContingency.FinitePower
variable {η α β σ : Type} [Ty η] [Ty α] [Ty β] [Ty σ]

def PowerClosed (Y : σ → Prop) : Prop :=
  ∀ A : σ → Prop, (∀ a, A a → Y a) → Smaller A Y →
    ∃ C : σ → Prop, (∀ c, C c → Y c) ∧ Smaller C Y ∧ Pow C A

def SmallAbove (H : η → Prop) (X : σ → Prop) : Prop :=
  ¬ ∃ Y : σ → Prop, (∀ y, Y y → X y) ∧ Smaller H Y ∧ PowerClosed Y

/-- H is the existing INEXACT inductive carrier over individuals. -/
def Small (X : σ → Prop) : Prop := SmallAbove (@Ordinal e _) X

/-- A schematic finite-tower invariant. The type σ is a metalinguistic
parameter, never an object-language quantifier. -/
def PowerBound (H : η → Prop) (A : α → Prop) (σ : Type) [Ty σ] : Prop :=
  ∀ Y : σ → Prop, Smaller H Y → PowerClosed Y → Smaller A Y

theorem powerClosed_lift (Y : σ → Prop) (A : α → Prop) (B : β → Prop)
    (closed : PowerClosed Y) (small : Smaller A Y) (power : Pow B A) : Smaller B Y := by
  obtain ⟨F,hf⟩ := small.1
  have imageBij := injects_bijects_image A Y F hf
  have backward : Embeds (RelImage F) A :=
    ⟨_,(bijects_inverse A (RelImage F) F imageBij).1⟩
  have imageSmall : Smaller (RelImage F) Y :=
    ⟨embeds_of_subset _ _ (image_subset F A Y hf.1),
      fun h => small.2 (embeds_trans Y (RelImage F) A h backward)⟩
  obtain ⟨C,sub,hC,powC⟩ := closed (RelImage F) (image_subset F A Y hf.1) imageSmall
  obtain ⟨G,hG⟩ := pow_equinumerous A B C power (pow_transfer_from_image A Y C F hf powC)
  have forward : Embeds B C := ⟨G,hG.1⟩
  exact ⟨embeds_trans B C Y forward hC.1,
    fun h => hC.2 (embeds_trans Y B C h forward)⟩

theorem powerBound_base (H : η → Prop) : PowerBound H H σ := fun _ h _ => h

theorem powerBound_step (H : η → Prop) (A : α → Prop) (B : β → Prop)
    (bound : PowerBound H A σ) (power : Pow B A) : PowerBound H B σ :=
  fun Y hY closed => powerClosed_lift Y A B closed (bound Y hY closed) power

theorem smallAbove_of_powerBound (H : η → Prop) (A : α → Prop) (X : σ → Prop)
    (bound : PowerBound H A σ) (embed : Embeds X A) : SmallAbove H X := by
  intro ⟨Y,sub,large,closed⟩
  exact (bound Y large closed).2 (embeds_trans Y X A (embeds_of_subset Y X sub) embed)

theorem smallAbove_of_embeds_benchmark (H : η → Prop) (X : σ → Prop)
    (embed : Embeds X H) : SmallAbove H X :=
  smallAbove_of_powerBound H H X (powerBound_base H) embed

theorem smallAbove_of_embeds_power (H : η → Prop) (A : α → Prop) (X : σ → Prop)
    (power : Pow A H) (embed : Embeds X A) : SmallAbove H X :=
  smallAbove_of_powerBound H A X (powerBound_step H H A (powerBound_base H) power) embed

theorem smallAbove_of_embeds_twoPowers (H : η → Prop) (A : α → Prop)
    (B : β → Prop) (X : σ → Prop) (first : Pow A H) (second : Pow B A)
    (embed : Embeds X B) : SmallAbove H X :=
  smallAbove_of_powerBound H B X
    (powerBound_step H A B (powerBound_step H H A (powerBound_base H) first) second) embed

/-- The proposed unboxed MP instance, using the native complete Boolean
algebra and relational order-isomorphism definitions. -/
def MPAt (σ : Type) [Ty σ] : Prop :=
  ∀ B E, @CBA σ _ B E → Small B →
    ∃ p I, OrderIso I B E (Below p) EntailmentOrder

#classicism_check powerClosed_lift powerBound_base powerBound_step smallAbove_of_powerBound smallAbove_of_embeds_benchmark smallAbove_of_embeds_power smallAbove_of_embeds_twoPowers
#classicism_types powerClosed_lift powerBound_base powerBound_step smallAbove_of_powerBound smallAbove_of_embeds_benchmark smallAbove_of_embeds_power smallAbove_of_embeds_twoPowers
end Classicism.MathematicalContingency.FinitePower
