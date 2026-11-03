import Classicism.Tools.Schema
import Classicism.Syntax.Pure
import Classicism.Principles.Recursion

/-!
# Church recursion principles as object-language schemas

As with `Certified/Arithmetic.lean`, these additional schemas are kept in their
own module and imported by the map's statement generator. The quoter checks the
reading of each statement against its shallow definition at every admitted type.
There are no axioms or omitted proofs of the recursion implications here.
-/

#classicism_schema
  Classicism.P.ChurchNumeralInfinity Classicism.P.NecChurchNumeralInfinity
  Classicism.P.ChurchNumeralFunctionalRecursion Classicism.P.SequenceFunctionalRecursion

namespace Classicism.P

/-- Church Numeral Infinity, read in any signature. -/
@[reducible] def ChurchNumeralInfinity.schemaIn {Sig : Classicism.Meta.Signature} :
    Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure ChurchNumeralInfinity.schema

/-- Boxed Church Numeral Infinity, read in any signature. -/
@[reducible] def NecChurchNumeralInfinity.schemaIn {Sig : Classicism.Meta.Signature} :
    Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure NecChurchNumeralInfinity.schema

/-- Church Numeral Functional Recursion, read in any signature. -/
@[reducible] def ChurchNumeralFunctionalRecursion.schemaIn {Sig : Classicism.Meta.Signature} :
    Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure ChurchNumeralFunctionalRecursion.schema

/-- Sequence Functional Recursion, read in any signature. -/
@[reducible] def SequenceFunctionalRecursion.schemaIn {Sig : Classicism.Meta.Signature} :
    Classicism.Meta.AxiomSet Sig :=
  Classicism.Meta.AxiomSet.ofPure SequenceFunctionalRecursion.schema

end Classicism.P
