import Classicism.Tools.Schema
import Classicism.Syntax.Pure
import Classicism.Syntax.ClosedTypes
import Classicism.Principles.ExactLower

/-!
# Quoted schemas for the exact/at-least comparison

Use the native Classicism quoter, reflection checks and schema generator.
Each principle is a closed sentence at type e, then included in arbitrary
signatures by the established ofPure operation.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

#classicism_schema Classicism.P.NecessaryLowerPeanoE
  Classicism.P.ExactPeanoE Classicism.P.ExactLowerBijectionE

namespace Classicism.P

@[reducible] def NecessaryLowerPeanoE.schemaIn
    {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure NecessaryLowerPeanoE.schema

@[reducible] def ExactPeanoE.schemaIn
    {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure ExactPeanoE.schema

@[reducible] def ExactLowerBijectionE.schemaIn
    {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure ExactLowerBijectionE.schema

/-- The quoted principle uses only closed object types. -/
theorem NecessaryLowerPeanoE.schema_closedTypes :
    Classicism.Meta.AxiomSet.ClosedTypes NecessaryLowerPeanoE.schema := by
  rintro a rfl
  simp [NecessaryLowerPeanoE.quoted, Classicism.Meta.Term.closedTypes]

theorem ExactPeanoE.schema_closedTypes :
    Classicism.Meta.AxiomSet.ClosedTypes ExactPeanoE.schema := by
  rintro a rfl
  simp [ExactPeanoE.quoted, Classicism.Meta.Term.closedTypes]

theorem ExactLowerBijectionE.schema_closedTypes :
    Classicism.Meta.AxiomSet.ClosedTypes ExactLowerBijectionE.schema := by
  rintro a rfl
  simp [ExactLowerBijectionE.quoted, Classicism.Meta.Term.closedTypes]

end Classicism.P
