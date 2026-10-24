import Classicism.Models.OldNewFailures
import Classicism.Certified.Signatures

/-!
# C + full unboxed ND + full BC does not entail IC or RC

Original formalization (misc), 22 October 2026. The countermodel is the
concrete OldNew.model. Its admission, soundness and exact quoted verdicts
are proved in the imported construction, not passed as assumptions.
The owning source and all record YAML remain unchanged.
-/

namespace Classicism.Meta.Intensional.OldNew

open AxiomSet
noncomputable section

abbrev Background : AxiomSet Signature.pure :=
  P.NecessityOfDistinctness.schema ∪ P.BooleanCompleteness.schema

theorem holds_nd_schema : model.HoldsAx P.NecessityOfDistinctness.schema := by
  rintro _ ⟨σ, _, rfl⟩
  exact root_nd σ

theorem holds_bc_schema : model.HoldsAx P.BooleanCompleteness.schema := by
  rintro _ ⟨ρ, _, rfl⟩
  exact root_bc ρ

theorem holds_background : model.HoldsAx Background :=
  model.holdsAx_union holds_nd_schema holds_bc_schema

theorem holds_nd_schemaIn : model.HoldsAx P.NecessityOfDistinctness.schemaIn :=
  (model.holdsAx_schemaIn_iff P.NecessityOfDistinctness.schema).2 holds_nd_schema

theorem holds_bc_schemaIn : model.HoldsAx P.BooleanCompleteness.schemaIn :=
  (model.holdsAx_schemaIn_iff P.BooleanCompleteness.schema).2 holds_bc_schema

theorem background_consistent : Background.Consistent :=
  AxiomSet.Consistent.of_model model isModel holds_background

theorem not_theorem_ic_et :
    ¬ Theorem (C.axioms ∪ Background) (P.InextensibleComprehension.quoted et) :=
  model.not_theorem_of_model isModel holds_background not_ic_et

theorem not_theorem_rc_et :
    ¬ Theorem (C.axioms ∪ Background) (P.RigidComprehension.quoted et) :=
  model.not_theorem_of_model isModel holds_background not_rc_et

theorem not_entails_ic : ¬ (Background ⟹ P.InextensibleComprehension.schema) :=
  fun h => not_theorem_ic_et (h _ ⟨et, ⟨trivial, trivial⟩, rfl⟩)

theorem not_entails_rc : ¬ (Background ⟹ P.RigidComprehension.schema) :=
  fun h => not_theorem_rc_et (h _ ⟨et, ⟨trivial, trivial⟩, rfl⟩)

/-- The central concrete semantic conjunction. Both positive premises are
full schemas; both failures are at et. No positive premise is boxed. -/
theorem central_countermodel :
    model.IsModel ∧ model.HoldsAx P.NecessityOfDistinctness.schema ∧
    model.HoldsAx P.BooleanCompleteness.schema ∧
    ¬ model.HoldsSentence (P.InextensibleComprehension.quoted et) ∧
    ¬ model.HoldsSentence (P.RigidComprehension.quoted et) :=
  ⟨isModel, holds_nd_schema, holds_bc_schema, not_ic_et, not_rc_et⟩

end
end Classicism.Meta.Intensional.OldNew
