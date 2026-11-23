import Classicism.Results.MathematicalContingency.FinitePowerSmallness
import Classicism.Results.MathematicalContingency.MPInterval
import Classicism.Results.MathematicalContingency.PropositionConeTransport
import Classicism.Results.MathematicalContingency.RegularOpenCones

/-! Current MP supplies nonzero proposition cones for a nonempty small forcing
completion. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {α β : Type} [Ty α] [Ty β]

theorem small_mp_interval_zero (mp : MPAt β) (B : β → Prop) (R : β → β → Prop)
    (cba : CBA B R) (small : Small B) (o : β) (member : B o)
    (least : ∀ b, B b → R o b) :
    ∃ p F, OrderIso F B R (Below p) EntailmentOrder ∧ F o False := by
  obtain ⟨p,F,iso⟩ := mp B R cba small
  exact ⟨p,F,iso,intervalIso_bottom_false B R F p iso o member least⟩

theorem small_mp_propositionCones (mp : MPAt β)
    (Q : α → Prop) (E : α → α → Prop) (B : β → Prop) (R : β → β → Prop)
    (o : β) (C : α → β → Prop) (cba : CBA B R) (small : Small B)
    (member : B o) (least : ∀ b, B b → R o b)
    (cones : DenseCones Q E B R o C) (inhabited : ∃ q, Q q) :
    ∃ p F, OrderIso F B R (Below p) EntailmentOrder ∧ F o False ∧ p ≠ False ∧
      PropositionCones Q E (RelCompose C F) p := by
  obtain ⟨p,F,iso,zero⟩ := small_mp_interval_zero mp B R cba small o member least
  have pc := denseCones_propositionCones Q E B R o C F p cones iso zero
  exact ⟨p,F,iso,zero,propositionCones_nonzero Q E (RelCompose C F) p pc inhabited,pc⟩

theorem small_regularOpen_propositionCones (mp : MPAt (α → Prop))
    (Q : α → Prop) (E : α → α → Prop) (order : PartialOrderOn Q E)
    (rc : P.RigidComprehension (α → Prop)) (small : Small (ROCarrier Q E))
    (inhabited : ∃ q, Q q) :
    ∃ p F o i, Endpoints (ROCarrier Q E) (ROOrder Q E) o i ∧
      OrderIso F (ROCarrier Q E) (ROOrder Q E) (Below p) EntailmentOrder ∧
      F o False ∧ p ≠ False ∧ PropositionCones Q E (RelCompose (ROCone Q E) F) p := by
  have completion := regularOpen_completion Q E order rc
  obtain ⟨o,i,he,_⟩ := completion.1.2.2.2.2
  obtain ⟨p,F,iso,zero,nonzero,pc⟩ := small_mp_propositionCones mp Q E _ _ o (ROCone Q E)
    completion.1 small he.1 (fun b hb => (he.2.2 b hb).1)
    (completion.2 o i he).1 inhabited
  exact ⟨p,F,o,i,he,iso,zero,nonzero,pc⟩

#classicism_check small_mp_interval_zero small_mp_propositionCones small_regularOpen_propositionCones
#classicism_types small_mp_interval_zero small_mp_propositionCones small_regularOpen_propositionCones
end Classicism.MathematicalContingency.FinitePower
