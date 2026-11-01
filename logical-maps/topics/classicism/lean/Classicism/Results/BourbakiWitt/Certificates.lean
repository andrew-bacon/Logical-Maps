import Classicism.Results.BourbakiWitt.NecessaryTransversal
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema
import Classicism.Certified.Schemas

/-!
# The results resting on the Bourbaki–Witt lemma, certified

The gate and the type-system check over the lemma's module and the results' modules; each
result derived in the object language and read as an entailment between schemas
(`foo.entails`).
-/

#classicism_audit Classicism.Background.BourbakiWitt Classicism.Results.BourbakiWitt.NecessaryTransversal
#classicism_types_audit Classicism.Background.BourbakiWitt Classicism.Results.BourbakiWitt.NecessaryTransversal

set_option maxHeartbeats 0 in
#classicism_derive Classicism.Proofs.BWTransversal.boolean_completeness_and_modalized_relational_choice_imply_necessary_transversal

#classicism_entails Classicism.Proofs.BWTransversal.boolean_completeness_and_modalized_relational_choice_imply_necessary_transversal

#check @Classicism.Proofs.BWTransversal.boolean_completeness_and_modalized_relational_choice_imply_necessary_transversal.entails
