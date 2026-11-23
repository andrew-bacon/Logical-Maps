import Classicism.Results.MathematicalContingency.NaturalHartogsIteration
import Classicism.Results.MathematicalContingency.ForcingGraphPowerBounds
import Classicism.Results.MathematicalContingency.RegularOpenPowerBounds
import Classicism.Results.MathematicalContingency.HartogsCommonBound
import Classicism.Results.MathematicalContingency.UniformCCC

set_option synthInstance.maxSize 4000
set_option maxRecDepth 20000

/-! The two original forcing carriers and their concrete regular-open carriers
are small under the new definition. The abbreviations below name existing
types and carriers, not new foundations. All package conjuncts are explicit
current RC instances; no size or order witness is packaged as an assumption.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026. -/
namespace Classicism.MathematicalContingency.FinitePower
variable {σ : Type} [Ty σ]

abbrev NumericalObject := (e → Prop) → Prop
abbrev FirstHartogsObject := OrdinalCarrier NumericalObject
abbrev SecondHartogsObject := OrdinalCarrier FirstHartogsObject
abbrev FirstHartogs := HartogsCarrier (@LowerNat e _)
abbrev SecondHartogs := HartogsCarrier FirstHartogs
abbrev PositiveGraph := CountableBitGraph e FirstHartogsObject
abbrev NegativeGraph := CohenGraph e SecondHartogsObject
abbrev PositiveForcing (I : FirstHartogsObject → Prop) : PositiveGraph → Prop := CountableBitCarrier I
abbrev PositiveOrder (I : FirstHartogsObject → Prop) : PositiveGraph → PositiveGraph → Prop := CountableBitOrder I
abbrev NegativeForcing : NegativeGraph → Prop := CohenCondition SecondHartogs
abbrev NegativeOrder : NegativeGraph → NegativeGraph → Prop := ConditionOrder LowerNat SecondHartogs ConditionBit

def ForcingSizeRC : Prop :=
  P.RigidComprehension (NumericalObject → Prop) ∧
  P.RigidComprehension ((NumericalObject → Prop) → Prop) ∧
  P.RigidComprehension (FirstHartogsObject → Prop) ∧
  P.RigidComprehension (FirstHartogsObject → FirstHartogsObject → Prop) ∧
  P.RigidComprehension ((FirstHartogsObject → Prop) → Prop) ∧
  P.RigidComprehension (SecondHartogsObject → Prop) ∧
  P.RigidComprehension (SecondHartogsObject → SecondHartogsObject → Prop) ∧
  P.RigidComprehension ((SecondHartogsObject → Prop) → Prop)

theorem firstHartogs_commonBound (hp : LowerPeano e)
    (rc : P.RigidComprehension (FirstHartogsObject → Prop))
    (rp : P.RigidComprehension (FirstHartogsObject → FirstHartogsObject → Prop)) :
    CommonPairedBound (@LowerNat e _) FirstHartogs :=
  commonPairedBound_of_pairing LowerNat FirstHartogs (HartogsOrder LowerNat)
    (hartogs_wellOrder rc LowerNat) (lowerNat_hartogs_pairing hp rc rp)
    (wellOrder_embeds_hartogs rc LowerNat LowerLT (lowerNat_wellOrder hp))
    (AtLeastZero e) (SucCard (AtLeastZero e)) lowerNat_zero (lowerNat_suc _ lowerNat_zero)
    (lowerNat_ne_suc_self hp _ lowerNat_zero)

theorem secondHartogs_commonBound (hp : LowerPeano e)
    (rc1 : P.RigidComprehension (FirstHartogsObject → Prop))
    (rp1 : P.RigidComprehension (FirstHartogsObject → FirstHartogsObject → Prop))
    (rc2 : P.RigidComprehension (SecondHartogsObject → Prop))
    (rp2 : P.RigidComprehension (SecondHartogsObject → SecondHartogsObject → Prop)) :
    CommonPairedBound (@LowerNat e _) SecondHartogs := by
  have two : ∃ a b : NumericalObject, LowerNat a ∧ LowerNat b ∧ a ≠ b :=
    ⟨AtLeastZero e,SucCard (AtLeastZero e),lowerNat_zero,lowerNat_suc _ lowerNat_zero,
      lowerNat_ne_suc_self hp _ lowerNat_zero⟩
  have closed := iterated_hartogs_closedSegments LowerNat LowerLT (lowerNat_wellOrder hp)
    ⟨LowerPair,lowerPair_pairing hp⟩ two rc1 rp1
  exact doubleHartogs_commonPairedBound_nontrivial LowerNat LowerLT (lowerNat_wellOrder hp)
    LowerPair (lowerPair_pairing hp) two rc1 rp1 rc2 rp2 closed.1 closed.2

theorem firstHartogs_sizeBound (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    PowerBound (@Ordinal e _) FirstHartogs σ :=
  lowerNat_hartogs_powerBound hp rcs.1 rcs.2.1

theorem secondHartogs_sizeBound (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    PowerBound (@Ordinal e _) SecondHartogs σ := by
  obtain ⟨rn,rnn,rh,rp,rhh,_,_,_⟩ := rcs
  exact lowerNat_secondHartogs_powerBound hp rn rnn rh rp rhh

theorem positive_forcing_embeds_power (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x) :
    Embeds (PositiveForcing I) (RigidPower FirstHartogs) := by
  obtain ⟨_,_,rh,rp,_,_,_,_⟩ := rcs
  exact countableBit_embeds_of_commonPairedBound I FirstHartogs
    (firstHartogs_commonBound hp rh rp) sub rh

theorem negative_forcing_embeds_power (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    Embeds NegativeForcing (RigidPower SecondHartogs) := by
  obtain ⟨_,_,rh1,rp1,_,rh2,rp2,_⟩ := rcs
  exact cohen_embeds_of_commonPairedBound SecondHartogs
    (secondHartogs_commonBound hp rh1 rp1 rh2 rp2) rh2

theorem positive_forcing_powerBound (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x) :
    PowerBound (@Ordinal e _) (PositiveForcing I) σ :=
  powerBound_of_embeds Ordinal _ _ (positive_forcing_embeds_power hp rcs I sub)
    (powerBound_step Ordinal FirstHartogs _ (firstHartogs_sizeBound hp rcs)
      (pow_rigidPower FirstHartogs rcs.2.2.1))

theorem negative_forcing_powerBound (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    PowerBound (@Ordinal e _) NegativeForcing σ :=
  powerBound_of_embeds Ordinal _ _ (negative_forcing_embeds_power hp rcs)
    (powerBound_step Ordinal SecondHartogs _ (secondHartogs_sizeBound hp rcs)
      (pow_rigidPower SecondHartogs rcs.2.2.2.2.2.1))

theorem positive_completion_embeds_twoPowers (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x) :
    Embeds (ROCarrier (PositiveForcing I) (PositiveOrder I))
      (RigidPower (RigidPower FirstHartogs)) :=
  roCarrier_embeds_power_of_embeds _ _ _ rcs.2.2.2.2.1
    (positive_forcing_embeds_power hp rcs I sub)

theorem negative_completion_embeds_twoPowers (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    Embeds (ROCarrier NegativeForcing NegativeOrder)
      (RigidPower (RigidPower SecondHartogs)) :=
  roCarrier_embeds_power_of_embeds _ _ _ rcs.2.2.2.2.2.2.2
    (negative_forcing_embeds_power hp rcs)

theorem positive_completion_powerBound (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x) :
    PowerBound (@Ordinal e _) (ROCarrier (PositiveForcing I) (PositiveOrder I)) σ :=
  roCarrier_powerBound Ordinal _ _ (RigidPower FirstHartogs) rcs.2.2.2.2.1
    (powerBound_step Ordinal FirstHartogs _ (firstHartogs_sizeBound hp rcs)
      (pow_rigidPower FirstHartogs rcs.2.2.1))
    (positive_forcing_embeds_power hp rcs I sub)

theorem negative_completion_powerBound (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    PowerBound (@Ordinal e _) (ROCarrier NegativeForcing NegativeOrder) σ :=
  roCarrier_powerBound Ordinal _ _ (RigidPower SecondHartogs) rcs.2.2.2.2.2.2.2
    (powerBound_step Ordinal SecondHartogs _ (secondHartogs_sizeBound hp rcs)
      (pow_rigidPower SecondHartogs rcs.2.2.2.2.2.1))
    (negative_forcing_embeds_power hp rcs)

theorem positive_forcing_and_completion_small (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (sub : ∀ x, I x → FirstHartogs x) :
    Small (PositiveForcing I) ∧ Small (ROCarrier (PositiveForcing I) (PositiveOrder I)) :=
  ⟨smallAbove_of_powerBound Ordinal _ _ (positive_forcing_powerBound hp rcs I sub) (embeds_refl _),
    smallAbove_of_powerBound Ordinal _ _ (positive_completion_powerBound hp rcs I sub) (embeds_refl _)⟩

theorem negative_forcing_and_completion_small (hp : LowerPeano e) (rcs : ForcingSizeRC) :
    Small NegativeForcing ∧ Small (ROCarrier NegativeForcing NegativeOrder) :=
  ⟨smallAbove_of_powerBound Ordinal _ _ (negative_forcing_powerBound hp rcs) (embeds_refl _),
    smallAbove_of_powerBound Ordinal _ _ (negative_completion_powerBound hp rcs) (embeds_refl _)⟩

theorem stable_positive_forcing_and_completion_small (hp : LowerPeano e) (rcs : ForcingSizeRC)
    (I : FirstHartogsObject → Prop) (LI : FirstHartogsObject → FirstHartogsObject → Prop)
    (stable : StableHartogsPresentation (@LowerNat e _) I LI) :
    Small (PositiveForcing I) ∧ Small (ROCarrier (PositiveForcing I) (PositiveOrder I)) :=
  positive_forcing_and_completion_small hp rcs I (fun x hx => (stable.2.2.1 x).mp hx)

#classicism_check firstHartogs_commonBound secondHartogs_commonBound firstHartogs_sizeBound
  secondHartogs_sizeBound positive_forcing_embeds_power negative_forcing_embeds_power
  positive_forcing_powerBound negative_forcing_powerBound positive_completion_embeds_twoPowers
  negative_completion_embeds_twoPowers positive_completion_powerBound negative_completion_powerBound
  positive_forcing_and_completion_small negative_forcing_and_completion_small
  stable_positive_forcing_and_completion_small
#classicism_types firstHartogs_commonBound secondHartogs_commonBound firstHartogs_sizeBound
  secondHartogs_sizeBound positive_forcing_embeds_power negative_forcing_embeds_power
  positive_forcing_powerBound negative_forcing_powerBound positive_completion_embeds_twoPowers
  negative_completion_embeds_twoPowers positive_completion_powerBound negative_completion_powerBound
  positive_forcing_and_completion_small negative_forcing_and_completion_small
  stable_positive_forcing_and_completion_small
end Classicism.MathematicalContingency.FinitePower
