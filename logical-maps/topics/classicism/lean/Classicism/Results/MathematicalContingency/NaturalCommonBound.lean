import Classicism.Results.MathematicalContingency.HartogsCommonBound
import Classicism.Results.MathematicalContingency.NaturalHartogsSmallness
import Classicism.Results.MathematicalContingency.NaturalPairing
set_option synthInstance.maxSize 2000
set_option maxRecDepth 20000
namespace Classicism.MathematicalContingency
variable {κ : Type} [Ty κ]
theorem natural_small_commonPairedBound (K : κ → Prop) (L : κ → κ → Prop)
    (inaccessible : StronglyInaccessible K L) (hp : LowerPeano e)
    (rcK : P.RigidComprehension (κ → Prop))
    (rcN : P.RigidComprehension (((e → Prop) → Prop) → Prop))
    (rc1 : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rp1 : P.RigidComprehension (OrdinalCarrier ((e → Prop) → Prop) → OrdinalCarrier ((e → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (rp2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop)) → Prop))
    (closed1 : ∀ h, HartogsCarrier (@LowerNat e _) h → Embeds (ClosedSegment (HartogsCarrier (@LowerNat e _)) (HartogsOrder (@LowerNat e _)) h) (@LowerNat e _))
    (closed2 : ∀ j, HartogsCarrier (HartogsCarrier (@LowerNat e _)) j →
      Embeds (ClosedSegment (HartogsCarrier (HartogsCarrier (@LowerNat e _))) (HartogsOrder (HartogsCarrier (@LowerNat e _))) j) (HartogsCarrier (@LowerNat e _))) :
    CommonPairedBound (@LowerNat e _) (HartogsCarrier (HartogsCarrier (@LowerNat e _))) ∧
      Small K L (HartogsCarrier (HartogsCarrier (@LowerNat e _))) :=
  ⟨doubleHartogs_commonPairedBound_nontrivial LowerNat LowerLT (lowerNat_wellOrder hp) LowerPair (lowerPair_pairing hp)
    ⟨AtLeastZero e,SucCard (AtLeastZero e),lowerNat_zero,lowerNat_suc _ lowerNat_zero,
      lowerNat_ne_suc_self hp _ lowerNat_zero⟩ rc1 rp1 rc2 rp2 closed1 closed2,
   small_natural_doubleHartogs K L inaccessible hp rcK rcN rc1 rc2⟩
#classicism_check natural_small_commonPairedBound
#classicism_types natural_small_commonPairedBound
end Classicism.MathematicalContingency
