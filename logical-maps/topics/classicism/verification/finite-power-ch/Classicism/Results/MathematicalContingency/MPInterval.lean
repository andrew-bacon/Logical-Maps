import Classicism.Results.MathematicalContingency.DensityEntailment

/-!
An interval representation sends the specified algebra bottom to False.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
MP is applied only after the explicit smallness premise is supplied.
-/
namespace Classicism.MathematicalContingency
variable {κ β : Type} [Ty κ] [Ty β]

theorem intervalIso_bottom_false (B : β → Prop) (R : β → β → Prop)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder)
    (o : β) (member : B o) (least : ∀ b, B b → R o b) : F o False := by
  obtain ⟨q,_,hoq⟩ := iso.1.1.1.2.1 o member
  obtain ⟨z,hz,hzF⟩ := intervalIso_zero_exists B R F P iso
  obtain ⟨r,_,hzr⟩ := iso.1.1.1.2.1 z hz
  have hr : r = False := iso.1.1.1.2.2 z r False hzr hzF
  have h : EntailmentOrder q r := (iso.2 o z q r hoq hzr).mp (least z hz)
  have hn : □ (¬ q) := modal_K _ _ (modal_K _ _
    (nec% (fun (h : q → r) (hn : ¬ r) (hq : q) => hn (h hq))) h)
    ((box_not_eq r).mpr hr)
  exact (box_not_eq q).mp hn ▸ hoq

theorem mp_interval_zero (K : κ → Prop) (L : κ → κ → Prop)
    (mp : MPAt β K L) (B : β → Prop) (R : β → β → Prop)
    (cba : CBA B R) (small : Small K L B)
    (o : β) (member : B o) (least : ∀ b, B b → R o b) :
    ∃ P F, OrderIso F B R (Below P) EntailmentOrder ∧ F o False := by
  obtain ⟨P,F,iso⟩ := mp B R cba small
  exact ⟨P,F,iso,intervalIso_bottom_false B R F P iso o member least⟩

#classicism_check intervalIso_bottom_false mp_interval_zero
#classicism_types intervalIso_bottom_false mp_interval_zero
end Classicism.MathematicalContingency
