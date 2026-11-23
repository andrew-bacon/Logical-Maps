import Classicism.Results.MathematicalContingency.PairingTransport

/-!
Pull a current well-order back through a relational injection.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
No choice, rigidity or necessary-distinctness premise is used.
-/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def PullbackOrder (F : α → β → Prop) (L : β → β → Prop) : α → α → Prop :=
  ImageOrder (fun y x => F x y) L

theorem injects_pullback_wellOrder (A : α → Prop) (B : β → Prop)
    (F : α → β → Prop) (L : β → β → Prop)
    (injects : Injects F A B) (order : WellOrderOn B L) :
    WellOrderOn A (PullbackOrder F L) := by
  have imageOrder := wellOrder_restrict B (RelImage F) L order (image_subset F A B injects.1)
  have inverse := bijects_inverse A (RelImage F) F (injects_bijects_image A B F injects)
  have pullback := bijects_image_wellOrder (RelImage F) A (fun y x => F x y)
    (RestrictOrder L (RelImage F)) inverse imageOrder
  refine wellOrder_coext A A (ImageOrder (fun y x => F x y) (RestrictOrder L (RelImage F)))
    (PullbackOrder F L) pullback (fun _ => Iff.rfl) ?_
  intro x y
  constructor
  · intro h
    obtain ⟨u,v,hxu,hyv,_,_,huv⟩ := h
    exact ⟨u,v,hxu,hyv,huv⟩
  · intro h
    obtain ⟨u,v,hxu,hyv,huv⟩ := h
    exact ⟨u,v,hxu,hyv,⟨x,hxu⟩,⟨y,hyv⟩,huv⟩

theorem wellOrder_exists_of_embeds (A : α → Prop) (B : β → Prop)
    (L : β → β → Prop) (order : WellOrderOn B L) (bound : Embeds A B) :
    ∃ R, WellOrderOn A R := by
  obtain ⟨F,hF⟩ := bound
  exact ⟨PullbackOrder F L,injects_pullback_wellOrder A B F L hF order⟩

#classicism_check injects_pullback_wellOrder wellOrder_exists_of_embeds
#classicism_types injects_pullback_wellOrder wellOrder_exists_of_embeds
end Classicism.MathematicalContingency
