import Classicism.Results.MathematicalContingency.CountableBitDecisions
import Classicism.Results.MathematicalContingency.MPInterval
import Classicism.Results.MathematicalContingency.PropositionConeTransport
import Classicism.Results.MathematicalContingency.DecisionRepresentation

namespace Classicism.MathematicalContingency
variable {κ σ τ β : Type} [Ty κ] [Ty σ] [Ty τ] [Ty β]

theorem countableBitSetup_mp_local
    (K : κ → Prop) (L : κ → κ → Prop) (mp : MPAt β K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (hp : LowerPeano σ) (I : τ → Prop) (setup : CountableBitSetup (σ := σ) K L I)
    (rcConditions : P.RigidComprehension (CountableBitGraph σ τ → Prop))
    (H : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA H R)
    (cones : ∀ o i, Endpoints H R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) H R o C) :
    ∃ P F o i, Endpoints H R o i ∧ OrderIso F H R (Below P) EntailmentOrder ∧
      F o False ∧ P ≠ False ∧ LocalDecisions (@LowerNat σ _) P := by
  obtain ⟨o,i,he,hd,small⟩ := countableBitSetup_completion_decisions K L limit rcK hp I setup
    rcConditions H R C cba cones
  obtain ⟨P,F,hF,hzero⟩ := mp_interval_zero K L mp H R cba small o he.1
    (fun b hb => (he.2.2 b hb).1)
  have pc := denseCones_propositionCones (CountableBitCarrier I) (CountableBitOrder I)
    H R o C F P (cones o i he) hF hzero
  exact ⟨P,F,o,i,he,hF,hzero,
    propositionCones_nonzero (CountableBitCarrier I) (CountableBitOrder I) (RelCompose C F) P pc setup.2.2.2,
    binaryDecisions_local H R F P o i hF hzero hd⟩

#classicism_check countableBitSetup_mp_local
#classicism_types countableBitSetup_mp_local
end Classicism.MathematicalContingency
