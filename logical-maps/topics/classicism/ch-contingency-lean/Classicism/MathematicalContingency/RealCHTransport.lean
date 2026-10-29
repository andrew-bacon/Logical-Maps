import Classicism.MathematicalContingency.CardinalCH
import Classicism.MathematicalContingency.Targets

/-!
The existing real-structure CH target has exactly the generic cardinal content.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
These transport theorems do not assert existence of a RealStructure. That remains
a separate construction; each use under a box must also supply boxed transport
premises, not merely current embeddings.
-/
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

theorem ch_iff_cardinalCH (R : γ → Prop) (A : γ → γ → γ → Prop) (o i : γ) :
    CH R A o i ↔ CardinalCH (NaturalPart R A o i) R := Iff.rfl

theorem ch_of_cardinalCH_embeddings (N : α → Prop) (S : β → Prop)
    (R : γ → Prop) (A : γ → γ → γ → Prop) (o i : γ)
    (ch : CardinalCH N S) (continuum : Embeds R S)
    (naturals : Embeds N (NaturalPart R A o i)) : CH R A o i :=
  cardinalCH_of_embeddings N (NaturalPart R A o i) S R ch continuum naturals

theorem not_ch_of_cardinalCH_embeddings (N : α → Prop) (S : β → Prop)
    (R : γ → Prop) (A : γ → γ → γ → Prop) (o i : γ)
    (notCH : ¬ CardinalCH N S) (continuum : Embeds S R)
    (naturals : Embeds (NaturalPart R A o i) N) : ¬ CH R A o i :=
  not_cardinalCH_of_embeddings N (NaturalPart R A o i) S R notCH continuum naturals

#classicism_check ch_iff_cardinalCH ch_of_cardinalCH_embeddings not_ch_of_cardinalCH_embeddings
#classicism_types ch_iff_cardinalCH ch_of_cardinalCH_embeddings not_ch_of_cardinalCH_embeddings
end Classicism.MathematicalContingency
