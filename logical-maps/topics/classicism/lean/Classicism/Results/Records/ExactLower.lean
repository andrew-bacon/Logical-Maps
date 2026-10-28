import Classicism.Principles.ExactLower
import Classicism.Results.Research.ExactLowerPeanoTransfer

/-! Exact map statements, with no additional hypotheses.
GPT-6 Astra Pro (OpenAI), prompted by Andrew Bacon, 28 October 2026. -/
namespace Classicism.Proofs
open Classicism.P

/-- `necessary-lower-peano-implies-exact-peano-e`. -/
theorem necessary_lower_peano_implies_exact_peano_e :
    NecessaryLowerPeanoE → ExactPeanoE :=
  ExactLower.exactPeano_of_box_lowerPeano

/-- `necessary-lower-peano-implies-cardinality-bijection-e`. -/
theorem necessary_lower_peano_implies_cardinality_bijection_e :
    NecessaryLowerPeanoE → ExactLowerBijectionE :=
  ExactLower.exactLowerBijection_of_box_lowerPeano

/-- The earlier, weaker two-premise result, retained for compatibility. -/
theorem exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e :
    ExactPeanoE → NecessaryLowerPeanoE → ExactLowerBijectionE :=
  ExactLower.exactLowerBijection_of_necessary_lower_peano

#classicism_check necessary_lower_peano_implies_exact_peano_e
  necessary_lower_peano_implies_cardinality_bijection_e
  exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e
#classicism_types necessary_lower_peano_implies_exact_peano_e
  necessary_lower_peano_implies_cardinality_bijection_e
  exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e

end Classicism.Proofs
