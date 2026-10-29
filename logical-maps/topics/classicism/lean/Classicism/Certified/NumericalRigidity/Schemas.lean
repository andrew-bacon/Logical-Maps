import Classicism.Principles.NumericalRigidity
import Classicism.Certified.Signatures

#classicism_schema Classicism.P.NumericalRigidity Classicism.P.NecNumericalRigidity

namespace Classicism.P
@[reducible] def NumericalRigidity.schemaIn {Sig : Classicism.Meta.Signature} :
    Classicism.Meta.AxiomSet Sig := Classicism.Meta.AxiomSet.ofPure NumericalRigidity.schema
@[reducible] def NecNumericalRigidity.schemaIn {Sig : Classicism.Meta.Signature} :
    Classicism.Meta.AxiomSet Sig := Classicism.Meta.AxiomSet.ofPure NecNumericalRigidity.schema

theorem NumericalRigidity.schema_closedTypes :
    Classicism.Meta.AxiomSet.ClosedTypes NumericalRigidity.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  simp [NumericalRigidity.quoted, Classicism.Meta.Term.closedTypes, *]

theorem NecNumericalRigidity.schema_closedTypes :
    Classicism.Meta.AxiomSet.ClosedTypes NecNumericalRigidity.schema := by
  rintro a ⟨σ, hσ, rfl⟩
  simp [NecNumericalRigidity.quoted, Classicism.Meta.Term.closedTypes, *]
end Classicism.P
