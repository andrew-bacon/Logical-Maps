import Classicism.Results.MathematicalContingency.ChoiceBooleanDecisions
import Classicism.Results.MathematicalContingency.CountableChoiceClosure
import Classicism.Results.MathematicalContingency.SmallMPCones
import Classicism.Results.MathematicalContingency.SmallForcingCompletions
import Classicism.Results.MathematicalContingency.CountableRowSurjection
import Classicism.Results.MathematicalContingency.CardinalCHWellOrderedBound
import Classicism.Results.MathematicalContingency.UnboxedRCRigidity

/-! Positive cardinal CH from the new MP and two current relational-choice
instances. OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Classicism.MathematicalContingency.FinitePower
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]

theorem small_countable_mp_local (mp : MPAt β) (hp : LowerPeano σ) (I : τ → Prop)
    (codes : P.RelationalChoice ((σ → Prop) → Prop)
      (((σ → Prop) → Prop) → τ → ((σ → Prop) → Prop) → Prop))
    (steps : P.RelationalChoice (((σ → Prop) → Prop) → CountableBitGraph σ τ → Prop)
      (CountableBitGraph σ τ))
    (rcGraph : P.RigidComprehension (CountableBitGraph σ τ))
    (B : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA B R) (small : Small B)
    (cones : ∀ o i, Endpoints B R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) B R o C) :
    ∃ p F o i, Endpoints B R o i ∧ OrderIso F B R (Below p) EntailmentOrder ∧
      F o False ∧ p ≠ False ∧ LocalDecisions (@LowerNat σ _) p := by
  have closed := countableCondition_countablyClosed_of_relationalChoice hp LowerNat I ConditionBit
    codes rcGraph
  obtain ⟨o,i,he,hd⟩ := closure_binary_decisions_cba_of_relationalChoice hp
    (CountableBitCarrier I) (CountableBitOrder I) B R C steps closed cba cones
  obtain ⟨q,hq,_⟩ := countableCondition_empty (@LowerNat σ _) LowerNat I ConditionBit rcGraph
  obtain ⟨p,F,iso,zero,nonzero,_⟩ := small_mp_propositionCones mp
    (CountableBitCarrier I) (CountableBitOrder I) B R o C cba small he.1
    (fun b hb => (he.2.2 b hb).1) (cones o i he) ⟨q,hq⟩
  exact ⟨p,F,o,i,he,iso,zero,nonzero,binaryDecisions_local B R F p o i iso zero hd⟩

theorem small_countable_possible_surjects (mp : MPAt β) (hi : DraftBoxInfinity σ)
    (I : τ → Prop) (rigidN : Rigid (@LowerNat σ _)) (rigidI : Rigid I)
    (ndI : DomainND I) (large : ¬ Embeds I (@LowerNat σ _))
    (codes : P.RelationalChoice ((σ → Prop) → Prop)
      (((σ → Prop) → Prop) → τ → ((σ → Prop) → Prop) → Prop))
    (steps : P.RelationalChoice (((σ → Prop) → Prop) → CountableBitGraph σ τ → Prop)
      (CountableBitGraph σ τ))
    (rcGraph : P.RigidComprehension (CountableBitGraph σ τ))
    (B : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA B R) (small : Small B)
    (cones : ∀ o i, Endpoints B R o i →
      DenseCones (CountableBitCarrier I) (CountableBitOrder I) B R o C)
    (incompatible : ∀ o i, Endpoints B R o i →
      IncompatibleCones (CountableBitCarrier I) (CountableBitOrder I) B R o C)
    (rcNames : P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (rcFreeze : P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))
    (rcRows : P.RigidComprehension (τ → (((σ → Prop) → Prop) → Prop) → Prop))
    (rcN : □ (P.RigidComprehension (((σ → Prop) → Prop) → Prop)))
    (ic : P.IntensionalChoice (((σ → Prop) → Prop) → Prop)) :
    ◇ (∃ G, Surjects G I (RigidPower (@LowerNat σ _))) := by
  obtain ⟨p,F,o,i,he,iso,zero,_,dec⟩ := small_countable_mp_local mp (lowerPeano_of_box hi)
    I codes steps rcGraph B R C cba small cones
  obtain ⟨R₀,hr,co⟩ := rcFreeze (RigidPower (@LowerNat σ _))
  have preserved := localDecisions_preserves_power LowerNat R₀ p rigidN (lowerNat_nd hi)
    hr co (box_elim rcN) ic dec
  exact countable_completion_possible_surjects hi I rigidN rigidI ndI large rcGraph B R o C
    cba (cones o i he) (incompatible o i he) F p iso zero R₀ hr co preserved
    rcNames rcFreeze rcRows rcN

/-- The fixed first-Hartogs stable index has necessarily countable segments.
This finishes directly with the existing cardinal CH definition. -/
theorem positive_possible_cardinalCH_of_stable (mp : MPAt (PositiveGraph → Prop))
    (hi : DraftBoxInfinity e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (LI : FirstHartogsObject → FirstHartogsObject → Prop)
    (stable : StableHartogsPresentation (@LowerNat e _) I LI)
    (codes : P.RelationalChoice NumericalObject
      (NumericalObject → FirstHartogsObject → NumericalObject → Prop))
    (steps : P.RelationalChoice (NumericalObject → PositiveGraph → Prop) PositiveGraph)
    (rcGraph : P.RigidComprehension PositiveGraph)
    (rcCompletion : P.RigidComprehension (PositiveGraph → Prop))
    (rcNames : P.RigidComprehension (NumericalObject → Prop → Prop))
    (rcRows : P.RigidComprehension (FirstHartogsObject → (NumericalObject → Prop) → Prop))
    (rcN : □ (P.RigidComprehension (NumericalObject → Prop)))
    (ic : P.IntensionalChoice (NumericalObject → Prop)) :
    ◇ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) := by
  have completion := regularOpen_completion (PositiveForcing I) (PositiveOrder I)
    (countableConditionOrder_partialOrder LowerNat LowerNat I ConditionBit) rcCompletion
  have small := (stable_positive_forcing_and_completion_small (lowerPeano_of_box hi) rcs I LI stable).2
  have surjection := small_countable_possible_surjects mp hi I (lowerNat_rigid_of_rc rcs.1)
    stable.1 stable.2.2.2.2.1 stable.2.2.2.2.2.2.1 codes steps rcGraph
    (ROCarrier (PositiveForcing I) (PositiveOrder I)) (ROOrder (PositiveForcing I) (PositiveOrder I))
    (ROCone (PositiveForcing I) (PositiveOrder I)) completion.1 small
    (fun o i he => (completion.2 o i he).1) (fun o i he => (completion.2 o i he).2)
    rcNames rcs.2.1 rcRows rcN ic
  exact possible_cardinalCH_of_wellOrdered_surjection LowerNat (RigidPower LowerNat) I LI
    stable.2.2.2.2.2.1 stable.2.2.2.2.2.2.2 surjection

theorem positive_possible_cardinalCH (mp : MPAt (PositiveGraph → Prop))
    (hi : DraftBoxInfinity e) (rcs : ForcingSizeRC)
    (codes : P.RelationalChoice NumericalObject
      (NumericalObject → FirstHartogsObject → NumericalObject → Prop))
    (steps : P.RelationalChoice (NumericalObject → PositiveGraph → Prop) PositiveGraph)
    (rcGraph : P.RigidComprehension PositiveGraph)
    (rcCompletion : P.RigidComprehension (PositiveGraph → Prop))
    (rcNames : P.RigidComprehension (NumericalObject → Prop → Prop))
    (rcRows : P.RigidComprehension (FirstHartogsObject → (NumericalObject → Prop) → Prop))
    (rcPair : P.RigidComprehension (NumericalObject → NumericalObject → Prop))
    (rcMap : P.RigidComprehension (FirstHartogsObject → NumericalObject → Prop))
    (rcN : □ (P.RigidComprehension (NumericalObject → Prop)))
    (ic : P.IntensionalChoice (NumericalObject → Prop)) :
    ◇ (CardinalCH (@LowerNat e _) (RigidPower (@LowerNat e _))) := by
  obtain ⟨I,LI,stable⟩ := natural_stable_hartogs_presentation hi (lowerNat_rigid_of_rc rcs.1)
    rcs.1 rcPair rcs.2.2.1 rcs.2.2.2.1 rcMap
  exact positive_possible_cardinalCH_of_stable mp hi rcs I LI stable codes steps rcGraph
    rcCompletion rcNames rcRows rcN ic

#classicism_check small_countable_mp_local small_countable_possible_surjects
  positive_possible_cardinalCH_of_stable positive_possible_cardinalCH
#classicism_types small_countable_mp_local small_countable_possible_surjects
  positive_possible_cardinalCH_of_stable positive_possible_cardinalCH
end Classicism.MathematicalContingency.FinitePower
