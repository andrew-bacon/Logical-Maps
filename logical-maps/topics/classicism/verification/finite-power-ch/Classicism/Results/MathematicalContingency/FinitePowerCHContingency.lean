import Classicism.Results.MathematicalContingency.SmallPositiveForcing
import Classicism.Results.MathematicalContingency.SmallNegativeForcing

/-! Cardinal CH contingency with explicit finite instances of the proposed
principles. This is a native source theorem, not a generated-map certificate.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency.FinitePower

/-- No inaccessible carrier, condition well-order, stable-index witness,
completion witness, or separate numerical-rigidity premise is assumed. -/
theorem cardinalCH_contingency
    (positiveMP : MPAt (PositiveGraph → Prop)) (negativeMP : MPAt (NegativeGraph → Prop))
    (hi : DraftBoxInfinity e) (rcs : ForcingSizeRC)
    (codes : P.RelationalChoice NumericalObject
      (NumericalObject → FirstHartogsObject → NumericalObject → Prop))
    (steps : P.RelationalChoice (NumericalObject → PositiveGraph → Prop) PositiveGraph)
    (rcPositive : P.RigidComprehension PositiveGraph)
    (rcPositiveCompletion : P.RigidComprehension (PositiveGraph → Prop))
    (rcNegative : P.RigidComprehension NegativeGraph)
    (rcNegativeCompletion : P.RigidComprehension (NegativeGraph → Prop))
    (rcNames : P.RigidComprehension (NumericalObject → Prop → Prop))
    (rcRows : P.RigidComprehension (FirstHartogsObject → (NumericalObject → Prop) → Prop))
    (rcPair : P.RigidComprehension (NumericalObject → NumericalObject → Prop))
    (rcMap : P.RigidComprehension (FirstHartogsObject → NumericalObject → Prop))
    (rcNamePair : P.RigidComprehension ((NumericalObject → Prop) → NumericalObject → Prop))
    (rcN : □ (P.RigidComprehension (NumericalObject → Prop)))
    (icPositive : P.IntensionalChoice (NumericalObject → Prop))
    (icNegative : P.IntensionalChoice ((NumericalObject → Prop) → NumericalObject → Prop))
    (icPower : P.IntensionalChoice ((NumericalObject → Prop) → (NumericalObject → Prop) → Prop)) :
    (◇ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _)))) ∧
      ◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) :=
  ⟨positive_possible_cardinalCH positiveMP hi rcs codes steps rcPositive rcPositiveCompletion
      rcNames rcRows rcPair rcMap rcN icPositive,
    negative_possible_not_cardinalCH negativeMP hi rcs rcNegative rcNegativeCompletion
      rcNames rcN icNegative rcPair icPower rcNamePair⟩

#classicism_check cardinalCH_contingency
#classicism_types cardinalCH_contingency
end Classicism.MathematicalContingency.FinitePower
