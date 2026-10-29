import Classicism.Results.MathematicalContingency.RegularOpenCones
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

/-- Hide the concrete regular-open witnesses before instantiating large forcing
condition types. This retains all completion outputs in a compact interface. -/
theorem regularOpen_exists (Q : α → Prop) (E : α → α → Prop)
    (hp : PartialOrderOn Q E) (rc : P.RigidComprehension (α → Prop)) :
    ∃ (B : (α → Prop) → Prop) (R : (α → Prop) → (α → Prop) → Prop)
      (C : α → (α → Prop) → Prop), CBA B R ∧
      ∀ o i, Endpoints B R o i → DenseCones Q E B R o C ∧ IncompatibleCones Q E B R o C :=
  ⟨ROCarrier Q E,ROOrder Q E,ROCone Q E,regularOpen_completion Q E hp rc⟩

#classicism_check regularOpen_exists
#classicism_types regularOpen_exists
end Classicism.MathematicalContingency
