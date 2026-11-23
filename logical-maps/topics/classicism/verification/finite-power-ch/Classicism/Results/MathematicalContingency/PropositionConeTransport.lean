import Classicism.Results.MathematicalContingency.BooleanDecisions
import Classicism.Results.MathematicalContingency.CohenSeparation
import Classicism.Results.MathematicalContingency.DensityEntailment
import Classicism.Results.MathematicalContingency.CarrierTheory

/-!
Proposition-valued cones are obtained by relational composition.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
The completion and interval representation remain explicit hypotheses. No
separate partial-order, completeness, modal map, rigidity, RC or IC assumption
is needed for the generic composition lemma. In the Cohen specialization,
current RC is used only for the already certified empty-condition witness.
-/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

/-- Transport the maps, nonzero values, monotonicity and density of basic cones
through the current interval isomorphism. The local-refinement clause of
DenseCones is not needed for these four PropositionCones requirements. -/
theorem denseCones_propositionCones (Q : α → Prop) (E : α → α → Prop)
    (B : β → Prop) (R : β → β → Prop) (o : β) (C : α → β → Prop)
    (F : β → Prop → Prop) (P : Prop)
    (cones : DenseCones Q E B R o C)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False) :
    PropositionCones Q E (RelCompose C F) P := by
  refine ⟨maps_compose C F Q B (Below P) cones.1 iso.1.1.1,?_,?_,?_⟩
  · intro d p hp
    obtain ⟨b,hdb,hbp⟩ := hp
    exact fun h => cones.2.1 d b hdb
      ((intervalIso_zero_iff B R F P iso o b p zero hbp).mpr h)
  · intro d e p q hp hq hed
    obtain ⟨b,hdb,hbp⟩ := hp
    obtain ⟨c,hec,hcq⟩ := hq
    exact (iso.2 c b q p hcq hbp).mp (cones.2.2.1 d e b c hdb hec hed)
  · intro q nonzero below
    obtain ⟨b,hb,hbq⟩ := iso.1.2.2 q below
    have hn : b ≠ o := fun h => nonzero
      ((intervalIso_zero_iff B R F P iso o b q zero hbq).mp h)
    obtain ⟨d,c,hd,hdc,hcb⟩ := cones.2.2.2.1 b hb hn
    obtain ⟨p,_,hcp⟩ := iso.1.1.1.2.1 c (cones.1.1 d c hdc).2
    exact ⟨d,p,hd,⟨c,hdc,hcp⟩,(iso.2 c b p q hcp hbq).mp hcb⟩

/-- A nonempty condition carrier makes the representing proposition possible. -/
theorem propositionCones_nonzero (Q : α → Prop) (E : α → α → Prop)
    (C : α → Prop → Prop) (P : Prop) (cones : PropositionCones Q E C P)
    (inhabited : ∃ d, Q d) : P ≠ False := by
  obtain ⟨d,hd⟩ := inhabited
  obtain ⟨q,hq,hdq⟩ := cones.1.2.1 d hd
  exact dia_mono q P hq (cones.2.1 d q hdq)

/-- In the Cohen application both the proposition cones and nonzero P are
derived inputs. Empty I is allowed: the empty condition still exists. -/
theorem cohen_denseCones_propositionCones {σ : Type} [Ty σ] (I : α → Prop)
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → α → Prop → Prop))
    (B : β → Prop) (R : β → β → Prop) (o : β)
    (C : (((σ → Prop) → Prop) → α → Prop → Prop) → β → Prop)
    (F : β → Prop → Prop) (P : Prop)
    (cones : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) B R o C)
    (iso : OrderIso F B R (Below P) EntailmentOrder) (zero : F o False) :
    PropositionCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit)
      (RelCompose C F) P ∧ P ≠ False := by
  have h := denseCones_propositionCones (CohenCondition I)
    (ConditionOrder LowerNat I ConditionBit) B R o C F P cones iso zero
  obtain ⟨d,hd,_⟩ := cohenCondition_empty I rc
  exact ⟨h,propositionCones_nonzero (CohenCondition I)
    (ConditionOrder LowerNat I ConditionBit) (RelCompose C F) P h ⟨d,hd⟩⟩

#classicism_check denseCones_propositionCones propositionCones_nonzero cohen_denseCones_propositionCones
#classicism_types denseCones_propositionCones propositionCones_nonzero cohen_denseCones_propositionCones
end Classicism.MathematicalContingency
