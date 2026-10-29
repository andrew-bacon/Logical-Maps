import Classicism.Statements
import Classicism.Certified.NumericalRigidity.Entailed

namespace Classicism.Numerical
open Classicism.Meta Classicism.Meta.AxiomSet
/-- Pure schema entailments lift to every admitted signature. -/
theorem entails_ofPure {Sig : Signature} {A B : AxiomSet Signature.pure} (h : A ⟹ B) :
    AxiomSet.ofPure (Sig := Sig) A ⟹ AxiomSet.ofPure B := by
  rintro a ⟨p, hp, rfl⟩
  exact Derivable.mono (ofPure_union_subset A) (Theorem.ofPure (h p hp))
end Classicism.Numerical

namespace Classicism.Map
open Classicism.Meta.AxiomSet
theorem countable_boolean_completeness_implies_numerical_rigidity : Statements.countable_boolean_completeness_implies_numerical_rigidity :=
  fun _ _ h => Entails.trans h (Numerical.entails_ofPure Numerical.countable_boolean_completeness_implies_numerical_rigidity.entails)
#print axioms countable_boolean_completeness_implies_numerical_rigidity

theorem boolean_completeness_implies_numerical_rigidity : Statements.boolean_completeness_implies_numerical_rigidity :=
  fun _ _ h => Entails.trans h (Numerical.entails_ofPure Numerical.boolean_completeness_implies_numerical_rigidity.entails)
#print axioms boolean_completeness_implies_numerical_rigidity

theorem necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity : Statements.necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity :=
  fun _ _ h => Entails.trans h (Numerical.entails_ofPure Numerical.necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity.entails)
#print axioms necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity

theorem necessary_boolean_completeness_implies_necessary_numerical_rigidity : Statements.necessary_boolean_completeness_implies_necessary_numerical_rigidity :=
  fun _ _ h => Entails.trans h (Numerical.entails_ofPure Numerical.necessary_boolean_completeness_implies_necessary_numerical_rigidity.entails)
#print axioms necessary_boolean_completeness_implies_necessary_numerical_rigidity

theorem rigid_comprehension_implies_necessary_numerical_rigidity : Statements.rigid_comprehension_implies_necessary_numerical_rigidity :=
  fun _ _ h => Entails.trans h (Numerical.entails_ofPure Numerical.rigid_comprehension_implies_necessary_numerical_rigidity.entails)
#print axioms rigid_comprehension_implies_necessary_numerical_rigidity

theorem necessary_numerical_rigidity_implies_numerical_rigidity : Statements.necessary_numerical_rigidity_implies_numerical_rigidity :=
  fun _ _ h => Entails.trans h (Numerical.entails_ofPure Numerical.necessary_numerical_rigidity_implies_numerical_rigidity.entails)
#print axioms necessary_numerical_rigidity_implies_numerical_rigidity

end Classicism.Map
