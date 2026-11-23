import Classicism.Results.MathematicalContingency.CommonPairedBound
import Classicism.Results.MathematicalContingency.NaturalHartogsSmallness
import Classicism.Results.MathematicalContingency.StableHartogsIndex

namespace Classicism.MathematicalContingency
variable {κ α β σ : Type} [Ty κ] [Ty α] [Ty β] [Ty σ]

theorem index_small_commonPairedBound
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (N : α → Prop) (LN : α → α → Prop) (hwN : WellOrderOn N LN)
    (Q : α → α → α → Prop) (hq : PairingOn N Q)
    (rcN : P.RigidComprehension (α → Prop)) (smallN : Small K L N)
    (a b : α) (ha : N a) (hb : N b) (hne : a ≠ b)
    (I : β → Prop) (LI : β → β → Prop) (hwI : WellOrderOn I LI)
    (large : ¬ Embeds I N)
    (closed : ∀ i, I i → Embeds (ClosedSegment I LI i) N)
    (rcPair : P.RigidComprehension (β → β → Prop)) :
    CommonPairedBound N I ∧ Small K L I := by
  have emb := wellOrder_embeds_of_not_embeds N LN I LI hwN hwI large
  have pairing := pairing_of_closedSegment_bounds N I LI Q hwI hq large closed rcPair
  have segments : ∀ i, I i → Embeds (Segment I LI i) N := by
    intro i hi
    exact embeds_trans _ (ClosedSegment I LI i) N
      (embeds_of_subset _ _ (fun x hx => ⟨hx.1,Or.inr hx.2⟩)) (closed i hi)
  exact ⟨commonPairedBound_of_pairing N I LI hwI pairing emb a b ha hb hne,
    small_of_segment_bounds K L hk limit rcK N rcN I LI hwI segments smallN⟩

theorem natural_index_small_commonPairedBound
    (K : κ → Prop) (L : κ → κ → Prop) (hk : WellOrderOn K L)
    (limit : StrongLimit K L) (rcK : P.RigidComprehension (κ → Prop))
    (hp : LowerPeano σ) (rcN : P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (smallN : Small K L (@LowerNat σ _))
    (I : β → Prop) (LI : β → β → Prop) (hwI : WellOrderOn I LI)
    (large : ¬ Embeds I (@LowerNat σ _))
    (closed : ∀ i, I i → Embeds (ClosedSegment I LI i) (@LowerNat σ _))
    (rcPair : P.RigidComprehension (β → β → Prop)) :
    CommonPairedBound (@LowerNat σ _) I ∧ Small K L I :=
  index_small_commonPairedBound K L hk limit rcK LowerNat LowerLT (lowerNat_wellOrder hp)
    LowerPair (lowerPair_pairing hp) rcN smallN (AtLeastZero σ) (SucCard (AtLeastZero σ))
    lowerNat_zero (lowerNat_suc _ lowerNat_zero) (lowerNat_ne_suc_self hp _ lowerNat_zero)
    I LI hwI large closed rcPair

/-- The stable presentation supplies current order and uncountability; closed bounds remain the agreed premise. -/
theorem stable_natural_index_small_commonPairedBound
    (K : κ → Prop) (L : κ → κ → Prop) (inaccessible : StronglyInaccessible K L)
    (hp : LowerPeano e) (rcK : P.RigidComprehension (κ → Prop))
    (rcN : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (H I : β → Prop) (R LI : β → β → Prop)
    (stable : StableIndexPresentation (@LowerNat e _) H I R LI)
    (closed : ∀ i, I i → Embeds (ClosedSegment I LI i) (@LowerNat e _))
    (rcPair : P.RigidComprehension (β → β → Prop)) :
    CommonPairedBound (@LowerNat e _) I ∧ Small K L I :=
  natural_index_small_commonPairedBound K L inaccessible.1.1 inaccessible.2.2.2 rcK hp rcN
    (small_lowerNat_of_inaccessible K L inaccessible hp) I LI
    (box_elim stable.2.2.2.2.2.1) stable.2.2.2.2.2.2.1 closed rcPair

/-- Transport the original closed-segment bound to the rigid presentation. -/
theorem stableIndex_closedSegment_bounds
    (N : α → Prop) (H I : β → Prop) (R LI : β → β → Prop)
    (stable : StableIndexPresentation N H I R LI)
    (closed : ∀ i, H i → Embeds (ClosedSegment H R i) N) :
    ∀ i, I i → Embeds (ClosedSegment I LI i) N := by
  intro i hi
  exact embeds_trans (ClosedSegment I LI i) (ClosedSegment H R i) N
    (embeds_of_subset _ _ (fun x hx =>
      ⟨(stable.2.2.1 x).mp hx.1,
        hx.2.elim Or.inl (fun h => Or.inr ((stable.2.2.2.1 x i).mp h))⟩))
    (closed i ((stable.2.2.1 i).mp hi))

#classicism_check index_small_commonPairedBound natural_index_small_commonPairedBound stable_natural_index_small_commonPairedBound stableIndex_closedSegment_bounds
#classicism_types index_small_commonPairedBound natural_index_small_commonPairedBound stable_natural_index_small_commonPairedBound stableIndex_closedSegment_bounds
end Classicism.MathematicalContingency
