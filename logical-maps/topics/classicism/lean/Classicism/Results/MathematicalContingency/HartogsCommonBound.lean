import Classicism.Results.MathematicalContingency.CommonPairedBoundNontrivial
import Classicism.Results.MathematicalContingency.DoubleHartogsPieces
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]
theorem doubleHartogs_commonPairedBound (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (a b : α) (ha : A a) (hb : A b) (hne : a ≠ b)
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → OrdinalCarrier (OrdinalCarrier α) → Prop))
    (closed1 : ∀ h, HartogsCarrier A h → Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) h) A)
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier A) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier A)) (HartogsOrder (HartogsCarrier A)) j) (HartogsCarrier A)) :
    CommonPairedBound A (HartogsCarrier (HartogsCarrier A)) :=
  commonPairedBound_of_pairing A (HartogsCarrier (HartogsCarrier A))
    (HartogsOrder (HartogsCarrier A)) (hartogs_wellOrder rc2 (HartogsCarrier A))
    (doubleHartogs_pairing_closed A Q hq rc1 rp1 rc2 rp2 closed1 closed2)
    (doubleHartogs_embeds_base A L hw rc1 rc2)
    a b ha hb hne
theorem doubleHartogs_commonPairedBound_nontrivial (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (two : ∃ a b, A a ∧ A b ∧ a ≠ b)
    (rc1 : P.RigidComprehension (OrdinalCarrier α → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → OrdinalCarrier (OrdinalCarrier α) → Prop))
    (closed1 : ∀ h, HartogsCarrier A h → Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) h) A)
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier A) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier A)) (HartogsOrder (HartogsCarrier A)) j) (HartogsCarrier A)) :
    CommonPairedBound A (HartogsCarrier (HartogsCarrier A)) :=
  commonPairedBound_of_nontrivial A (HartogsCarrier (HartogsCarrier A))
    (HartogsOrder (HartogsCarrier A)) (hartogs_wellOrder rc2 (HartogsCarrier A))
    (doubleHartogs_pairing_closed A Q hq rc1 rp1 rc2 rp2 closed1 closed2)
    (doubleHartogs_embeds_base A L hw rc1 rc2)
    two
#classicism_check doubleHartogs_commonPairedBound_nontrivial
#classicism_types doubleHartogs_commonPairedBound_nontrivial
#classicism_check doubleHartogs_commonPairedBound
#classicism_types doubleHartogs_commonPairedBound
end Classicism.MathematicalContingency
