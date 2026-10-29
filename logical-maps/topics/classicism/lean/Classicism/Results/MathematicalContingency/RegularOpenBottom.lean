import Classicism.Results.MathematicalContingency.RegularOpenExistence
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

/-- Select the bottom before substituting a large condition type. -/
theorem regularOpen_exists_bottom (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    ∃ (B : (α → Prop) → Prop) (R : (α → Prop) → (α → Prop) → Prop)
      (o : α → Prop) (C : α → (α → Prop) → Prop),
      CBA B R ∧ DenseCones Q E B R o C ∧ IncompatibleCones Q E B R o C ∧
      B o ∧ (∀ U, B U → R o U) := by
  obtain ⟨B,R,C,cba,cones⟩ := regularOpen_exists Q E hp rc
  obtain ⟨o,i,he,_⟩ := cba.2.2.2.2
  exact ⟨B,R,o,C,cba,(cones o i he).1,(cones o i he).2,he.1,fun U hu => (he.2.2 U hu).1⟩

#classicism_check regularOpen_exists_bottom
#classicism_types regularOpen_exists_bottom
end Classicism.MathematicalContingency
