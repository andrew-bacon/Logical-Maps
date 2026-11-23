import Classicism.Results.MathematicalContingency.NaturalForcingPowerBounds
import Classicism.Results.MathematicalContingency.RegularOpenBoolean

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000

/-! Apply the proposed unboxed MP to the native regular-open completions.
These algebra representations do not yet assert either modal CH conclusion.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
namespace Classicism.MathematicalContingency.FinitePower

theorem positive_small_cba (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x)
    (rcCompletion : P.RigidComprehension (PositiveGraph → Prop)) :
    CBA (ROCarrier (PositiveForcing I) (PositiveOrder I)) (ROOrder (PositiveForcing I) (PositiveOrder I)) ∧
      Small (ROCarrier (PositiveForcing I) (PositiveOrder I)) :=
  ⟨regularOpen_cba _ _ (countableConditionOrder_partialOrder LowerNat LowerNat I ConditionBit)
    rcCompletion,(positive_forcing_and_completion_small hp rcs I sub).2⟩

theorem negative_small_cba (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (rcCompletion : P.RigidComprehension (NegativeGraph → Prop)) :
    CBA (ROCarrier NegativeForcing NegativeOrder) (ROOrder NegativeForcing NegativeOrder) ∧
      Small (ROCarrier NegativeForcing NegativeOrder) :=
  ⟨regularOpen_cba _ _ (cohenCondition_partialOrder SecondHartogs) rcCompletion,
    (negative_forcing_and_completion_small hp rcs).2⟩

theorem positive_MP_realization (mp : MPAt (PositiveGraph → Prop))
    (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x)
    (rcCompletion : P.RigidComprehension (PositiveGraph → Prop)) :
    ∃ p F, OrderIso F (ROCarrier (PositiveForcing I) (PositiveOrder I))
      (ROOrder (PositiveForcing I) (PositiveOrder I)) (Below p) EntailmentOrder := by
  have h := positive_small_cba hp rcs I sub rcCompletion
  exact mp _ _ h.1 h.2

theorem negative_MP_realization (mp : MPAt (NegativeGraph → Prop))
    (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (rcCompletion : P.RigidComprehension (NegativeGraph → Prop)) :
    ∃ p F, OrderIso F (ROCarrier NegativeForcing NegativeOrder)
      (ROOrder NegativeForcing NegativeOrder) (Below p) EntailmentOrder := by
  have h := negative_small_cba hp rcs rcCompletion
  exact mp _ _ h.1 h.2

#classicism_check positive_small_cba negative_small_cba positive_MP_realization negative_MP_realization
#classicism_types positive_small_cba negative_small_cba positive_MP_realization negative_MP_realization
end Classicism.MathematicalContingency.FinitePower
