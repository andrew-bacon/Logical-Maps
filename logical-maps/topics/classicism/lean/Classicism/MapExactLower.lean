import Classicism.Map
import Classicism.Certified.ExactLower

/-!
# The exact/lower map arrows at their generated statement types

Each proof cites a native object-language entailment. Classicism.Map's
map_cert lifts the pure entailment to every admitted signature and every
axiom set entailing the displayed premises. No shallow extensionality
axiom or additional arithmetic premise is inserted here.
-/
namespace Classicism.Map

theorem necessary_lower_peano_implies_exact_peano_e :
    Statements.necessary_lower_peano_implies_exact_peano_e := by
  map_cert Proofs.necessary_lower_peano_implies_exact_peano_e.entails

theorem necessary_lower_peano_implies_cardinality_bijection_e :
    Statements.necessary_lower_peano_implies_cardinality_bijection_e := by
  map_cert Proofs.necessary_lower_peano_implies_cardinality_bijection_e.entails

theorem exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e :
    Statements.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e := by
  map_cert Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e.entails

end Classicism.Map
