import Classicism.Results.MathematicalContingency.SerialCounting
import Classicism.Results.MathematicalContingency.PositiveOrderTypeCHBridge

/-! Least preimages turn a relational surjection from a well-order into a
reverse injection. No functional choice or extra comprehension is used. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem leastPreimage_injects (A : α → Prop) (B : β → Prop)
    (L : α → α → Prop) (F : α → β → Prop)
    (hw : WellOrderOn A L) (hf : Surjects F A B) :
    Injects (LeastRelated B A L (fun b a => F a b)) B A := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro b a h
    exact ⟨h.1,h.2.1⟩
  · intro b hb
    obtain ⟨a,ha⟩ := leastRelated_exists B A L (fun b a => F a b) hw hf.2 b hb
    exact ⟨a,ha.2.1,ha⟩
  · intro b a c ha hc
    exact leastRelated_unique B A L (fun b a => F a b) hw b a c ha hc
  · intro b c a hb hc
    exact hf.1.2.2 a b c hb.2.2.1 hc.2.2.1

theorem embeds_of_surjects_wellOrder (A : α → Prop) (B : β → Prop)
    (L : α → α → Prop) (F : α → β → Prop)
    (hw : WellOrderOn A L) (hf : Surjects F A B) : Embeds B A :=
  ⟨LeastRelated B A L (fun b a => F a b),leastPreimage_injects A B L F hw hf⟩

theorem possible_embeds_of_possible_surjects (A : α → Prop) (B : β → Prop)
    (L : α → α → Prop) (hw : □ (WellOrderOn A L))
    (surjection : ◇ (∃ F, Surjects F A B)) : ◇ (Embeds B A) :=
  dia_mono _ _ (modal_K _ _
    (nec% (fun (ha : WellOrderOn A L) (h : ∃ F, Surjects F A B) =>
      h.elim (fun F hf => embeds_of_surjects_wellOrder A B L F ha hf))) hw) surjection

theorem possible_rigidPower_equinumerous_hartogs_of_possible_surjects
    (N : α → Prop) (A : β → Prop) (L : β → β → Prop)
    (rcN : □ (P.RigidComprehension (α → Prop)))
    (rcH : □ (P.RigidComprehension (OrdinalCarrier α → Prop)))
    (hw : □ (WellOrderOn A L))
    (small : □ (∀ a, A a → Embeds (Segment A L a) N))
    (surjection : ◇ (∃ F, Surjects F A (RigidPower N))) :
    ◇ (Equinumerous (RigidPower N) (HartogsCarrier N)) :=
  possible_rigidPower_equinumerous_hartogs_of_possible_embeds N A L rcN rcH hw small
    (possible_embeds_of_possible_surjects A (RigidPower N) L hw surjection)

#classicism_check leastPreimage_injects embeds_of_surjects_wellOrder possible_embeds_of_possible_surjects possible_rigidPower_equinumerous_hartogs_of_possible_surjects
#classicism_types leastPreimage_injects embeds_of_surjects_wellOrder possible_embeds_of_possible_surjects possible_rigidPower_equinumerous_hartogs_of_possible_surjects
end Classicism.MathematicalContingency
