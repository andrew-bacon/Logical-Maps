import Classicism.Results.MathematicalContingency.DensityEntailment
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β : Type} [Ty α] [Ty β]

theorem maps_of_coext (A : α → Prop) (B : β → Prop) (J K : α → β → Prop)
    (h : J ≡ K) (hj : Maps J A B) : Maps K A B :=
  ⟨fun x y hk => hj.1 x y ((h x y).mpr hk),
    fun x hx => (hj.2.1 x hx).elim (fun y hy => ⟨y,hy.1,(h x y).mp hy.2⟩),
    fun x y z hy hz => hj.2.2 x y z ((h x y).mpr hy) ((h x z).mpr hz)⟩

theorem injects_coext_iff (A : α → Prop) (B : β → Prop) (J K : α → β → Prop)
    (h : J ≡ K) : Injects J A B ↔ Injects K A B := by
  constructor
  · intro hj
    exact ⟨maps_of_coext A B J K h hj.1,
      fun x z y hx hz => hj.2 x z y ((h x y).mpr hx) ((h z y).mpr hz)⟩
  · intro hk
    exact ⟨maps_of_coext A B K J (fun x y => (h x y).symm) hk.1,
      fun x z y hx hz => hk.2 x z y ((h x y).mp hx) ((h z y).mp hz)⟩

theorem injects_coextensionInvariant (A : α → Prop) (B : β → Prop) :
    CoextensionInvariant (fun J => Injects J A B) :=
  nec% (fun J K h => injects_coext_iff A B J K h)

/-- Local selection is applied to coextension-invariant injectivity, not to rigidity of a witness. -/
theorem local_injection_exclusion (A : α → Prop) (B : β → Prop) (P : Prop)
    (ic : Classicism.P.IntensionalChoice (α → β → Prop))
    (kill : ∀ Q, EntailmentOrder Q P → ∀ J : α → β → Prop,
      EntailmentOrder Q (Injects J A B) → Q = False) :
    EntailmentOrder P (¬ Embeds A B) := by
  let Q := P ∧ Embeds A B
  have hQP : EntailmentOrder Q P := nec% (fun h : Q => h.1)
  have hex : EntailmentOrder Q (∃ J, Injects J A B) := nec% (fun h : Q => h.2)
  obtain ⟨J,hJ⟩ := local_selection_binary ic Q (fun J => Injects J A B)
    (injects_coextensionInvariant A B) hex
  have hz : Q = False := kill Q hQP J hJ
  exact modal_K _ _ (nec% (fun (h : ¬ (P ∧ Embeds A B)) (hp : P) (he : Embeds A B) => h ⟨hp,he⟩))
    ((box_not_eq Q).mpr hz)

#classicism_check maps_of_coext injects_coext_iff injects_coextensionInvariant local_injection_exclusion
#classicism_types maps_of_coext injects_coext_iff injects_coextensionInvariant local_injection_exclusion
end Classicism.MathematicalContingency
