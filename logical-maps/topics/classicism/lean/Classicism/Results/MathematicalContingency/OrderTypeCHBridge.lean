import Classicism.Results.MathematicalContingency.CardinalCH
import Classicism.Results.MathematicalContingency.WellOrderCardinality
import Classicism.Results.MathematicalContingency.HartogsTheorem

/-! Cardinal consequences of the order-type formulation of CH.
All hypotheses are local to the evaluation world; no global well-ordering
or additional rigidity premise is used.
OpenAI Codex, prompted by Andrew Bacon. -/
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

theorem cardinalCH_of_wellOrder_segments (N : α → Prop) (H : β → Prop)
    (M : β → β → Prop) (hw : WellOrderOn H M)
    (small : ∀ h, H h → Embeds (Segment H M h) N) : CardinalCH N H := by
  intro X sub
  obtain hsmall | hlarge := wellOrder_small_or_larger N X (RestrictOrder M X) H M
    (wellOrder_restrict H X M hw sub) hw small
  · exact Or.inl hsmall
  · exact Or.inr (cantor_bernstein X H (embeds_of_subset X H sub) hlarge)

theorem cardinalCH_of_equinumerous_wellOrder_segments (N : α → Prop)
    (S : γ → Prop) (H : β → Prop) (M : β → β → Prop)
    (hw : WellOrderOn H M) (small : ∀ h, H h → Embeds (Segment H M h) N)
    (eq : Equinumerous S H) : CardinalCH N S := by
  obtain ⟨F,hF⟩ := eq
  exact cardinalCH_of_embeddings N N H S
    (cardinalCH_of_wellOrder_segments N H M hw small) ⟨F,hF.1⟩ (embeds_refl N)

theorem cardinalCH_of_equinumerous_hartogs (N : α → Prop) (S : β → Prop)
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (eq : Equinumerous S (HartogsCarrier N)) : CardinalCH N S :=
  cardinalCH_of_equinumerous_wellOrder_segments N S (HartogsCarrier N)
    (HartogsOrder N) (hartogs_wellOrder rc N) (hartogs_segment_embeds N) eq

theorem not_equinumerous_hartogs_of_not_cardinalCH (N : α → Prop) (S : β → Prop)
    (rc : P.RigidComprehension (OrdinalCarrier α → Prop))
    (notCH : ¬ CardinalCH N S) : ¬ Equinumerous S (HartogsCarrier N) :=
  fun eq => notCH (cardinalCH_of_equinumerous_hartogs N S rc eq)

/-- The comprehension premise is supplied at accessible worlds, not necessitated
from its actual-world truth. -/
theorem possible_not_equinumerous_hartogs_of_possible_not_cardinalCH
    (N : α → Prop) (S : β → Prop)
    (rc : □ (P.RigidComprehension (OrdinalCarrier α → Prop)))
    (notCH : ◇ (¬ CardinalCH N S)) : ◇ (¬ Equinumerous S (HartogsCarrier N)) :=
  dia_mono _ _
    (modal_K _ _ (nec% (fun (hrc : P.RigidComprehension (OrdinalCarrier α → Prop))
      (hn : ¬ CardinalCH N S) => not_equinumerous_hartogs_of_not_cardinalCH N S hrc hn)) rc)
    notCH

#classicism_check cardinalCH_of_wellOrder_segments cardinalCH_of_equinumerous_wellOrder_segments cardinalCH_of_equinumerous_hartogs not_equinumerous_hartogs_of_not_cardinalCH possible_not_equinumerous_hartogs_of_possible_not_cardinalCH
#classicism_types cardinalCH_of_wellOrder_segments cardinalCH_of_equinumerous_wellOrder_segments cardinalCH_of_equinumerous_hartogs not_equinumerous_hartogs_of_not_cardinalCH possible_not_equinumerous_hartogs_of_possible_not_cardinalCH
end Classicism.MathematicalContingency
