import Classicism.Results.MathematicalContingency.CardinalCH
import Classicism.Results.MathematicalContingency.WellOrderPullback
import Classicism.Results.MathematicalContingency.WellOrderCardinality
import Classicism.Results.MathematicalContingency.WellOrderSurjection

/-! Finite-Power CH Strategy: finish the positive branch directly in cardinal form.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
The box on preservation hypotheses is explicit; no choice is necessitated.
-/
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

theorem cardinalCH_of_wellOrdered_bound (N : α → Prop) (S : β → Prop)
    (I : γ → Prop) (L : γ → γ → Prop) (hw : WellOrderOn I L)
    (small : ∀ i, I i → Embeds (Segment I L i) N) (bound : Embeds S I) :
    CardinalCH N S := by
  intro X sub
  have hx : Embeds X I := embeds_trans X S I (embeds_of_subset X S sub) bound
  obtain ⟨R,hr⟩ := wellOrder_exists_of_embeds X I L hw hx
  obtain countable | large := wellOrder_small_or_larger N X R I L hr hw small
  · exact Or.inl countable
  · exact Or.inr (cantor_bernstein X S (embeds_of_subset X S sub)
      (embeds_trans S I X bound large))

theorem cardinalCH_of_wellOrdered_surjection (N : α → Prop) (S : β → Prop)
    (I : γ → Prop) (L : γ → γ → Prop) (hw : WellOrderOn I L)
    (small : ∀ i, I i → Embeds (Segment I L i) N)
    (surjection : ∃ F, Surjects F I S) : CardinalCH N S := by
  obtain ⟨F,hF⟩ := surjection
  exact cardinalCH_of_wellOrdered_bound N S I L hw small
    (embeds_of_surjects_wellOrder I S L F hw hF)

theorem possible_cardinalCH_of_wellOrdered_surjection (N : α → Prop) (S : β → Prop)
    (I : γ → Prop) (L : γ → γ → Prop) (hw : □ (WellOrderOn I L))
    (small : □ (∀ i, I i → Embeds (Segment I L i) N))
    (surjection : ◇ (∃ F, Surjects F I S)) : ◇ (CardinalCH N S) :=
  dia_mono _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (h : WellOrderOn I L) (s : ∀ i, I i → Embeds (Segment I L i) N)
      (f : ∃ F, Surjects F I S) => cardinalCH_of_wellOrdered_surjection N S I L h s f)) hw) small)
    surjection

#classicism_check cardinalCH_of_wellOrdered_bound cardinalCH_of_wellOrdered_surjection possible_cardinalCH_of_wellOrdered_surjection
#classicism_types cardinalCH_of_wellOrdered_bound cardinalCH_of_wellOrdered_surjection possible_cardinalCH_of_wellOrdered_surjection
end Classicism.MathematicalContingency
