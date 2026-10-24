import Classicism.Models.OldNewSeparation
import Classicism.Results.Research.RigidityClosureResearchSchemas

/-!
# Failure of full Tame Rigidity in the concrete old/new model

This separate assembly uses the independently authored, translated full-schema
ND + BC + TR -> RC theorem. The semantic countermodel itself is OldNew.model.
No claim of failure at a particular TR instance is made.
-/

namespace Classicism.Meta.Intensional.OldNew

open AxiomSet
noncomputable section

theorem not_tame_schema : ¬ model.HoldsAx P.TameRigidity.schema := by
  intro ht
  have hrc : model.HoldsAx P.RigidComprehension.schema :=
    model.entails_holds isModel Classicism.Meta.Research.RigidityClosure.tame_implies_rc
      (model.holdsAx_union holds_background ht)
  exact not_rc_et (hrc _ ⟨et, ⟨trivial, trivial⟩, rfl⟩)

theorem not_entails_tame : ¬ (Background ⟹ P.TameRigidity.schema) :=
  fun ht => not_tame_schema (model.entails_holds isModel ht holds_background)

end
end Classicism.Meta.Intensional.OldNew
