import Classicism.Results.MathematicalContingency.SmallForcingCompletions
import Classicism.Results.MathematicalContingency.SmallMPCones
import Classicism.Results.MathematicalContingency.ConditionWellOrder
import Classicism.Results.MathematicalContingency.CohenCompletionCH
import Classicism.Results.MathematicalContingency.UnboxedRCRigidity

/-! The negative branch reuses the native Cohen argument after proving its
smallness and structural inputs. No inaccessible bound or ordinary choice.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency.FinitePower

theorem negative_coordinate_bounds (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    ∃ K LK QK, CohenCoordinateBounds (@LowerNat e _) SecondHartogs K LK QK := by
  have two : ∃ a b : NumericalObject, LowerNat a ∧ LowerNat b ∧ a ≠ b :=
    ⟨AtLeastZero e,SucCard (AtLeastZero e),lowerNat_zero,lowerNat_suc _ lowerNat_zero,
      lowerNat_ne_suc_self hp _ lowerNat_zero⟩
  have closed := iterated_hartogs_closedSegments LowerNat LowerLT (lowerNat_wellOrder hp)
    ⟨LowerPair,lowerPair_pairing hp⟩ two rcs.2.2.1 rcs.2.2.2.1
  exact natural_hartogs_coordinate_bounds hp rcs.2.2.1 rcs.2.2.2.1 rcs.2.2.2.2.2.1 closed.1

theorem negative_possible_not_cardinalCH (mp : MPAt (NegativeGraph → Prop))
    (hi : DraftBoxInfinity e) (rcs : ForcingSizeRC)
    (rcGraph : P.RigidComprehension NegativeGraph)
    (rcCompletion : P.RigidComprehension (NegativeGraph → Prop))
    (rcNames : P.RigidComprehension (NumericalObject → Prop → Prop))
    (rcN : □ (P.RigidComprehension (NumericalObject → Prop)))
    (ic : P.IntensionalChoice ((NumericalObject → Prop) → NumericalObject → Prop))
    (rcPair : P.RigidComprehension (NumericalObject → NumericalObject → Prop))
    (icPower : P.IntensionalChoice ((NumericalObject → Prop) → (NumericalObject → Prop) → Prop))
    (rcNamePair : P.RigidComprehension ((NumericalObject → Prop) → NumericalObject → Prop)) :
    ◇ (¬ CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) := by
  have hp := lowerPeano_of_box hi
  have completion := regularOpen_completion NegativeForcing NegativeOrder
    (cohenCondition_partialOrder SecondHartogs) rcCompletion
  obtain ⟨o,i,he,_⟩ := completion.1.2.2.2.2
  obtain ⟨p,F,iso,zero⟩ := small_mp_interval_zero mp _ _ completion.1
    (negative_forcing_and_completion_small hp rcs).2 o he.1 (fun b hb => (he.2.2 b hb).1)
  obtain ⟨L,Q,u,v,hw,hq,hu,hv,hn,hN,hI,hBits⟩ := secondHartogs_commonBound hp
    rcs.2.2.1 rcs.2.2.2.1 rcs.2.2.2.2.2.1 rcs.2.2.2.2.2.2.1
  obtain ⟨LC,hwC⟩ := cohenCondition_wellOrder_of_pairing SecondHartogs SecondHartogs Q
    rcs.2.2.2.2.2.1 L hw hq u v hu hv hn hN hI hBits
  exact (cohen_not_cardinalCH_of_completion hi SecondHartogs rcGraph LC
    (ROCarrier NegativeForcing NegativeOrder) (ROOrder NegativeForcing NegativeOrder) o
    (ROCone NegativeForcing NegativeOrder) completion.1 hwC
    (completion.2 o i he).1 (completion.2 o i he).2 F p iso zero
    (lowerNat_rigid_of_rc rcs.1) rcNames rcs.2.1 rcN ic rcPair icPower rcNamePair
    (negative_coordinate_bounds hp rcs)).2

#classicism_check negative_coordinate_bounds negative_possible_not_cardinalCH
#classicism_types negative_coordinate_bounds negative_possible_not_cardinalCH
end Classicism.MathematicalContingency.FinitePower
