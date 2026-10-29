import Classicism.Results.MathematicalContingency.RigidImageCoding
import Classicism.Results.MathematicalContingency.BooleanConeCoding

/-!
Smallness under embeddings and rigid powers, and the dense-completion bound.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
StrongLimit and current RC at the bound's predicate type are explicit.
No regularity or initial-cardinal premise is needed for these transfers.
-/
namespace Classicism.MathematicalContingency
variable {κ α β γ : Type} [Ty κ] [Ty α] [Ty β] [Ty γ]

theorem small_of_embeds (K : κ → Prop) (L : κ → κ → Prop)
    (A : α → Prop) (B : β → Prop) (bound : Embeds A B) (small : Small K L B) :
    Small K L A := by
  obtain ⟨a,ha,ba⟩ := small
  exact ⟨a,ha,embeds_trans A B (Segment K L a) bound ba⟩

theorem small_rigidPower (K : κ → Prop) (L : κ → κ → Prop)
    (limit : StrongLimit K L) (rc : P.RigidComprehension (κ → Prop))
    (A : α → Prop) (small : Small K L A) : Small K L (RigidPower A) := by
  obtain ⟨a,ha,bound⟩ := small
  obtain ⟨b,hb,powerBound⟩ := limit a ha
  exact ⟨b,hb,embeds_trans (RigidPower A) (RigidPower (Segment K L a)) (Segment K L b)
    (rigidPower_embeds_of_embeds A (Segment K L a) rc bound) powerBound⟩

theorem small_of_embeds_rigidPower (K : κ → Prop) (L : κ → κ → Prop)
    (limit : StrongLimit K L) (rc : P.RigidComprehension (κ → Prop))
    (H : α → Prop) (A : β → Prop) (bound : Embeds H (RigidPower A)) (small : Small K L A) :
    Small K L H :=
  small_of_embeds K L H (RigidPower A) bound (small_rigidPower K L limit rc A small)

/-- Density supplies the completion-to-power embedding; the caller only
supplies a small bound for the condition carrier, not a new bound for B. -/
theorem denseCones_small (K : κ → Prop) (L : κ → κ → Prop)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop)
    (cba : CBA B R) (member : B o) (least : ∀ b, B b → R o b)
    (cones : DenseCones Q E B R o C) (J : γ → Prop)
    (rcJ : P.RigidComprehension (γ → Prop)) (bound : Embeds Q J) (small : Small K L J) :
    Small K L B :=
  small_of_embeds_rigidPower K L limit rcK B J
    (denseCones_embeds_rigidPower Q E B R o C cba member least cones J rcJ bound) small

#classicism_check small_of_embeds small_rigidPower small_of_embeds_rigidPower denseCones_small
#classicism_types small_of_embeds small_rigidPower small_of_embeds_rigidPower denseCones_small
end Classicism.MathematicalContingency
