import Classicism.Results.MathematicalContingency.CountableForcingBounds
import Classicism.Results.MathematicalContingency.PositiveIndexBound

namespace Classicism.MathematicalContingency
variable {κ σ τ : Type} [Ty κ] [Ty σ] [Ty τ]

abbrev CountableBitGraph (σ τ : Type) := ((σ → Prop) → Prop) → τ → Prop → Prop

def CountableBitCarrier (I : τ → Prop) (G : CountableBitGraph σ τ) : Prop :=
  CountableCondition (@LowerNat σ _) (@LowerNat σ _) I ConditionBit G

def CountableBitOrder (I : τ → Prop) (G H : CountableBitGraph σ τ) : Prop :=
  CountableConditionOrder (@LowerNat σ _) (@LowerNat σ _) I ConditionBit G H

def CountableBitSetup (K : κ → Prop) (L : κ → κ → Prop) (I : τ → Prop) : Prop :=
  (∃ LC, WellOrderOn (@CountableBitCarrier σ τ _ _ I) LC) ∧
  @CountablyClosed σ (CountableBitGraph σ τ) _ _ (CountableBitCarrier I) (CountableBitOrder I) ∧
  Small K L (@CountableBitCarrier σ τ _ _ I) ∧ ∃ G, @CountableBitCarrier σ τ _ _ I G

theorem countableBitSetup_of_common_bound
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (hp : LowerPeano σ) (I : τ → Prop)
    (bound : CommonPairedBound (@LowerNat σ _) I) (small : Small K L I)
    (rcI : P.RigidComprehension (τ → Prop))
    (rcCode : P.RigidComprehension (((σ → Prop) → Prop) → τ → ((σ → Prop) → Prop) → Prop))
    (rcGraph : P.RigidComprehension (CountableBitGraph σ τ)) :
    CountableBitSetup (σ := σ) K L I := by
  obtain ⟨LI,Q,u,v,hw,hq,hu,hv,hne,hN,hI,hBits⟩ := bound
  obtain ⟨G,hG,he⟩ := countableCondition_empty (@LowerNat σ _) LowerNat I ConditionBit rcGraph
  exact ⟨countableCondition_wellOrder_of_pairing K L hk limit rcK LowerNat LowerNat I ConditionBit
      I Q hq rcI small hN hI hBits,
    countableCondition_countablyClosed_of_small_pairing K L hk limit rcK hp LowerNat I ConditionBit
      I Q hq rcI small hN hI hN rcCode rcGraph,
    countableCondition_small_of_pairing K L limit rcK LowerNat LowerNat I ConditionBit
      I Q hq rcI small hN hI hBits, G,hG⟩

theorem stable_natural_countableBitSetup
    (K : κ → Prop) (L : κ → κ → Prop) (inaccessible : StronglyInaccessible K L)
    (hp : LowerPeano e) (rcK : P.RigidComprehension (κ → Prop))
    (rcN : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (H I : τ → Prop) (R LI : τ → τ → Prop)
    (stable : StableIndexPresentation (@LowerNat e _) H I R LI)
    (closed : ∀ i, I i → Embeds (ClosedSegment I LI i) (@LowerNat e _))
    (rcPair : P.RigidComprehension (τ → τ → Prop))
    (rcI : P.RigidComprehension (τ → Prop))
    (rcCode : P.RigidComprehension (((e → Prop) → Prop) → τ → ((e → Prop) → Prop) → Prop))
    (rcGraph : P.RigidComprehension (CountableBitGraph e τ)) :
    CountableBitSetup (σ := e) K L I := by
  obtain ⟨bound,small⟩ := stable_natural_index_small_commonPairedBound K L inaccessible hp rcK rcN
    H I R LI stable closed rcPair
  exact countableBitSetup_of_common_bound K L inaccessible.1.1 inaccessible.2.2.2 rcK hp I
    bound small rcI rcCode rcGraph

/-- The intended Hartogs-indexed instance, at the natural type used by inaccessibility. -/
theorem stable_hartogs_countableBitSetup
    (K : κ → Prop) (L : κ → κ → Prop) (inaccessible : StronglyInaccessible K L)
    (hp : LowerPeano e) (rcK : P.RigidComprehension (κ → Prop))
    (rcN : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (I : OrdinalCarrier ((e → Prop) → Prop) → Prop)
    (LI : OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)
    (stable : StableHartogsPresentation (@LowerNat e _) I LI)
    (closed : ∀ i, I i → Embeds (ClosedSegment I LI i) (@LowerNat e _))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcI : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcCode : P.RigidComprehension
      (((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcGraph : P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)))) :
    CountableBitSetup (σ := e) K L I :=
  stable_natural_countableBitSetup K L inaccessible hp rcK rcN (HartogsCarrier LowerNat) I
    (HartogsOrder LowerNat) LI stable closed rcPair rcI rcCode rcGraph

/-- The intended Hartogs-indexed instance, at the natural type used by inaccessibility. -/
theorem stable_hartogs_countableBitSetup_of_closedSegments
    (K : κ → Prop) (L : κ → κ → Prop) (inaccessible : StronglyInaccessible K L)
    (hp : LowerPeano e) (rcK : P.RigidComprehension (κ → Prop))
    (rcN : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (I : OrdinalCarrier ((e → Prop) → Prop) → Prop)
    (LI : OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop)
    (stable : StableHartogsPresentation (@LowerNat e _) I LI)
    (closed : ∀ i, HartogsCarrier (@LowerNat e _) i →
      Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) i) (@LowerNat e _))
    (rcPair : P.RigidComprehension
      (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcI : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rcCode : P.RigidComprehension
      (((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → ((e → Prop) → Prop) → Prop))
    (rcGraph : P.RigidComprehension (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)))) :
    CountableBitSetup (σ := e) K L I :=
  stable_hartogs_countableBitSetup K L inaccessible hp rcK rcN I LI stable
    (stableIndex_closedSegment_bounds LowerNat (HartogsCarrier LowerNat) I (HartogsOrder LowerNat)
      LI stable closed) rcPair rcI rcCode rcGraph

#classicism_check countableBitSetup_of_common_bound stable_natural_countableBitSetup stable_hartogs_countableBitSetup stable_hartogs_countableBitSetup_of_closedSegments
#classicism_types countableBitSetup_of_common_bound stable_natural_countableBitSetup stable_hartogs_countableBitSetup stable_hartogs_countableBitSetup_of_closedSegments
end Classicism.MathematicalContingency
