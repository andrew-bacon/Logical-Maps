import Classicism.Results.Research.ChoiceActuality
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Schema
import Classicism.Certified.Schemas

/-!
Requested finitary C certificates, pending sole-owner compilation. The sharp
result uses RC at `(t,t)` and BC at `tt`; the guarded intermediate uses RC at
`(tt,t)`. No map/YAML verification status is set by this source file.
-/

#classicism_audit Classicism.Results.Research.ChoiceActuality
#classicism_types_audit Classicism.Results.Research.ChoiceActuality

#classicism_derive Classicism.Research.Choice.guarded_chain_complete
  Classicism.Research.Choice.guarded_selector_impossible
  Classicism.Research.Choice.choice_completeness_actuality
  Classicism.Research.Choice.choice_completeness_actuality_sharp
  Classicism.Research.Choice.necessary_choice_completeness_actuality_sharp
  Classicism.Research.Choice.choice_completeness_transversal_sharp

#print axioms Classicism.Research.Choice.choice_completeness_actuality_sharp.derivable
#print axioms Classicism.Research.Choice.choice_completeness_transversal_sharp.derivable
