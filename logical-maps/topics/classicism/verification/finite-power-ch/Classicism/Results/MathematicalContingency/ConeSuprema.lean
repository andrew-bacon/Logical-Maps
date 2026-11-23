import Classicism.Results.MathematicalContingency.SupremumRepresentation
import Classicism.Results.MathematicalContingency.CarrierTheory

/-!
Suprema of selected basic cones.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Incompatibility preservation is an explicit additional completion output.
It is not a consequence of the existing DenseCones interface.
-/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def ConeGenerators (Q : α → Prop) (C : α → β → Prop) (D : α → Prop) (b : β) : Prop :=
  ∃ d, Q d ∧ D d ∧ C d b

def IncompatibleCones (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop) : Prop :=
  ∀ d e b c, C d b → C e c →
    (¬ ∃ f, Q f ∧ E f d ∧ E f e) → Meets B R b c o

theorem coneGenerators_sub (Q : α → Prop) (C : α → β → Prop)
    (B : β → Prop) (maps : Maps C Q B) (D : α → Prop) :
    ∀ b, ConeGenerators Q C D b → B b := by
  intro b h
  obtain ⟨d,_,_,hc⟩ := h
  exact (maps.1 d b hc).2

theorem coneSupremum_positive (Q : α → Prop) (C : α → β → Prop)
    (B : β → Prop) (R : β → β → Prop) (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder)
    (D : α → Prop) (p : Prop)
    (value : RepresentedSupremum B R (ConeGenerators Q C D) F p)
    (d : α) (q : Prop) (hd : Q d) (selected : D d) (cone : RelCompose C F d q) :
    EntailmentOrder q p := by
  obtain ⟨b,hdb,hbq⟩ := cone
  exact representedSupremum_above B R F P iso (ConeGenerators Q C D) p value
    b q ⟨d,hd,selected,hdb⟩ hbq

theorem coneSupremum_negative (Q : α → Prop) (E : α → α → Prop)
    (C : α → β → Prop) (B : β → Prop) (R : β → β → Prop) (o : β)
    (maps : Maps C Q B) (incompatible : IncompatibleCones Q E B R o C)
    (F : β → Prop → Prop) (P : Prop)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False)
    (D : α → Prop) (p : Prop)
    (value : RepresentedSupremum B R (ConeGenerators Q C D) F p)
    (d : α) (q : Prop) (cone : RelCompose C F d q)
    (opposite : ∀ e, Q e → D e → ¬ ∃ f, Q f ∧ E f d ∧ E f e) :
    EntailmentOrder q (¬ p) := by
  obtain ⟨c,hdc,hcq⟩ := cone
  refine representedSupremum_disjoint B R F P iso o zero (ConeGenerators Q C D)
    (coneGenerators_sub Q C B maps D) p value c q hcq ?_
  intro b hb
  obtain ⟨e,he,hD,heb⟩ := hb
  exact incompatible d e c b hdc heb (opposite e he hD)

#classicism_check coneGenerators_sub coneSupremum_positive coneSupremum_negative
#classicism_types coneGenerators_sub coneSupremum_positive coneSupremum_negative
end Classicism.MathematicalContingency
