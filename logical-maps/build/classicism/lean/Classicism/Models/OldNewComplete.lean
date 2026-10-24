import Classicism.Models.OldNewTame
import Classicism.Models.OldNewFutureBC

/-!
# The complete old/new separation package

Assembly of the concrete root and future proofs. The future module was
independently authored. No frozen source, owning record or original research
has been modified to obtain these statements.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory AxiomSet

theorem not_theorem_box_bc_et :
    ¬ Theorem (C.axioms ∪ Background) (Term.box (P.BooleanCompleteness.quoted et)) :=
  model.not_theorem_of_model isModel holds_background root_not_box_bc_et

theorem not_entails_box_bc : ¬ (Background ⟹ P.NecBooleanCompleteness.schema) :=
  fun h => not_theorem_box_bc_et (h _ ⟨et, ⟨trivial, trivial⟩, rfl⟩)

theorem complete_countermodel :
    model.IsModel ∧ model.HoldsAx Background ∧
    ¬ model.HoldsSentence (P.InextensibleComprehension.quoted et) ∧
    ¬ model.HoldsSentence (P.RigidComprehension.quoted et) ∧
    ¬ model.HoldsAx P.TameRigidity.schema ∧
    ¬ model.HoldsSentence (Term.box (P.BooleanCompleteness.quoted et)) ∧
    ∀ k : E ⟶ O, ¬ model.Holds k (P.BooleanCompleteness.quoted et) .nil :=
  ⟨isModel, holds_background, not_ic_et, not_rc_et, not_tame_schema,
    root_not_box_bc_et, future_not_bc_et⟩

end Classicism.Meta.Intensional.OldNew
