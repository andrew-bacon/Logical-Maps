import Classicism.Certified.ChurchRecursion

/-! Complete recursion implications at every relational output type.
The empty vector of output arguments includes proposition outputs. -/
namespace Classicism.Meta
open AxiomSet

theorem necessary_church_numeral_infinity_implies_church_numeral_functional_recursion :
    P.NecChurchNumeralInfinity.schema ⟹ P.ChurchNumeralFunctionalRecursion.schema := by
  rintro _ ⟨α, τ, hα, hτ, rfl⟩
  have h := Church.num_recursion_unary.listRule τ.args α hα
  have e : τ.args ⇒* RTy.t = τ := RTy.ofArgs_args τ
  rw [e] at h
  exact (Theorem.ofC h).mp (Theorem.ax ⟨α, hα, rfl⟩)

theorem necessary_church_numeral_infinity_implies_sequence_functional_recursion :
    P.NecChurchNumeralInfinity.schema ⟹ P.SequenceFunctionalRecursion.schema := by
  rintro _ ⟨α, σ, τ, hα, hσ, hτ, rfl⟩
  have h := Church.seq_recursion_unary.listRule τ.args α σ hα hσ
  have e : τ.args ⇒* RTy.t = τ := RTy.ofArgs_args τ
  rw [e] at h
  exact (Theorem.ofC h).mp (Theorem.ax ⟨α, hα, rfl⟩)

end Classicism.Meta
