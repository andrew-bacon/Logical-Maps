import Classicism.Results.MathematicalContingency.CountableBitSetup

namespace Classicism.MathematicalContingency
variable {κ σ τ β : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β]

theorem countableBitSetup_completion_decisions
    (K : κ → Prop) (L : κ → κ → Prop) (limit : StrongLimit K L)
    (rcK : P.RigidComprehension (κ → Prop)) (hp : LowerPeano σ) (I : τ → Prop)
    (setup : CountableBitSetup (σ := σ) K L I)
    (rcConditions : P.RigidComprehension (CountableBitGraph σ τ → Prop))
    (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA H R)
    (cones : ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C) :
    ∃ o i, Endpoints H R o i ∧ @BinaryDecisionProperty σ β _ _ H R o i ∧ Small K L H := by
  obtain ⟨LC,hw⟩ := setup.1
  obtain ⟨o,i,he,hd⟩ := closure_binary_decisions_cba hp (CountableBitCarrier I)
    (CountableBitOrder I) LC H R C hw setup.2.1 cba cones
  exact ⟨o,i,he,hd,denseCones_small K L limit rcK (CountableBitCarrier I)
    (CountableBitOrder I) H R o C cba he.1 (fun b hb => (he.2.2 b hb).1)
    (cones o i he) (CountableBitCarrier I) rcConditions (embeds_refl _) setup.2.2.1⟩

#classicism_check countableBitSetup_completion_decisions
#classicism_types countableBitSetup_completion_decisions
end Classicism.MathematicalContingency
