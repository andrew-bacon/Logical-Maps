import Classicism.Results.MathematicalContingency.SmallForcingCompletions

/-! Compose the generic regular-open CBA theorem with the new unboxed MP.
Keeping the construction generic avoids an expanded concrete-CBA conjunction
in the negative branch's certificate. All original hypotheses are retained.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Classicism.MathematicalContingency.FinitePower

theorem regularOpen_MP_realization_generic {σ : Type} [Ty σ]
    (W : σ → Prop) (E : σ → σ → Prop)
    (mp : MPAt (σ → Prop)) (po : PartialOrderOn W E)
    (rc : P.RigidComprehension (σ → Prop)) (small : Small (ROCarrier W E)) :
    ∃ p I, OrderIso I (ROCarrier W E) (ROOrder W E) (Below p) EntailmentOrder :=
  mp _ _ (regularOpen_cba W E po rc) small

theorem negative_MP_realization_via_generic
    (mp : MPAt (NegativeGraph → Prop)) (hp : LowerPeano e)
    (rcs : ForcingSizeRC) (rcCompletion : P.RigidComprehension (NegativeGraph → Prop)) :
    ∃ p F, OrderIso F (ROCarrier NegativeForcing NegativeOrder)
      (ROOrder NegativeForcing NegativeOrder) (Below p) EntailmentOrder :=
  regularOpen_MP_realization_generic NegativeForcing NegativeOrder mp
    (cohenCondition_partialOrder SecondHartogs) rcCompletion
    (negative_forcing_and_completion_small hp rcs).2

#classicism_check regularOpen_MP_realization_generic negative_MP_realization_via_generic
#classicism_types regularOpen_MP_realization_generic negative_MP_realization_via_generic

end Classicism.MathematicalContingency.FinitePower
