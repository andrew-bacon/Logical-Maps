import Classicism.Results.MathematicalContingency.WellOrderTrichotomy

/-! Generic comparison wrapper to keep higher-type certification bounded.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

theorem wellOrder_proper_segment_of_not_embeds (A : α → Prop) (L : α → α → Prop)
    (B : β → Prop) (M : β → β → Prop) (ha : WellOrderOn A L) (hb : WellOrderOn B M)
    (hne : ¬ Embeds B A) :
    ∃ b, B b ∧ ∃ F, OrderIso F A L (Segment B M b) (RestrictOrder M (Segment B M b)) := by
  obtain ⟨F,hF⟩ | hseg | ⟨a,_,F,hF⟩ := wellOrder_trichotomy A L B M ha hb
  · exact (hne ⟨_,(orderIso_inverse A B L M F hF).1.1⟩).elim
  · exact hseg
  · exact (hne (embeds_trans B _ A ⟨F,hF.1.1⟩ (embeds_of_subset _ _ (fun _ h => h.1)))).elim

theorem wellOrder_embeds_of_not_embeds (A : α → Prop) (L : α → α → Prop)
    (B : β → Prop) (M : β → β → Prop) (ha : WellOrderOn A L) (hb : WellOrderOn B M)
    (hne : ¬ Embeds B A) : Embeds A B := by
  obtain ⟨b,_,F,hF⟩ := wellOrder_proper_segment_of_not_embeds A L B M ha hb hne
  exact embeds_trans A _ B ⟨F,hF.1.1⟩ (embeds_of_subset _ _ (fun _ h => h.1))

variable {γ : Type} [Ty γ]

theorem wellOrder_embeds_from_segment_bounds (A : α → Prop) (B : β → Prop) (L : β → β → Prop)
    (H : γ → Prop) (M : γ → γ → Prop) (hw : WellOrderOn B L) (hh : WellOrderOn H M)
    (hne : ¬ Embeds H A) (small : ∀ b, B b → Embeds (Segment B L b) A) : Embeds B H := by
  obtain ⟨F,hF⟩ | ⟨a,_,F,hF⟩ | ⟨b,hb,F,hF⟩ := wellOrder_trichotomy B L H M hw hh
  · exact ⟨F,hF.1.1⟩
  · exact embeds_trans B _ H ⟨F,hF.1.1⟩ (embeds_of_subset _ _ (fun _ h => h.1))
  · exact (hne (embeds_trans H _ A ⟨F,hF.1.1⟩ (small b hb))).elim

theorem wellOrder_small_or_larger (A : α → Prop) (B : β → Prop) (L : β → β → Prop)
    (H : γ → Prop) (M : γ → γ → Prop) (hw : WellOrderOn B L) (hh : WellOrderOn H M)
    (small : ∀ h, H h → Embeds (Segment H M h) A) : Embeds B A ∨ Embeds H B := by
  obtain ⟨F,hF⟩ | ⟨a,ha,F,hF⟩ | ⟨b,_,F,hF⟩ := wellOrder_trichotomy B L H M hw hh
  · exact Or.inr ⟨_,(orderIso_inverse B H L M F hF).1.1⟩
  · exact Or.inl (embeds_trans B _ A ⟨F,hF.1.1⟩ (small a ha))
  · exact Or.inr (embeds_trans H _ B ⟨F,hF.1.1⟩ (embeds_of_subset _ _ (fun _ h => h.1)))


#classicism_check wellOrder_proper_segment_of_not_embeds wellOrder_embeds_of_not_embeds wellOrder_embeds_from_segment_bounds wellOrder_small_or_larger
#classicism_types wellOrder_proper_segment_of_not_embeds wellOrder_embeds_of_not_embeds wellOrder_embeds_from_segment_bounds wellOrder_small_or_larger
end Classicism.MathematicalContingency
