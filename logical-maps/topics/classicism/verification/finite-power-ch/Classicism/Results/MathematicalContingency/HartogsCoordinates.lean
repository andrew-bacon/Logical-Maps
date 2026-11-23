import Classicism.Results.MathematicalContingency.PairingTransport
import Classicism.Results.MathematicalContingency.HartogsBounds
import Classicism.Results.MathematicalContingency.PairWellOrder
namespace Classicism.MathematicalContingency
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

/-- Precisely the coordinate bounds used by the two Cohen obstruction arguments. -/
def CohenCoordinateBounds (A : α → Prop) (I K : β → Prop)
    (L : β → β → Prop) (Q : β → β → β → Prop) : Prop :=
  (∀ x, K x → I x) ∧ WellOrderOn K L ∧ PairingOn K Q ∧
    Embeds A K ∧ ¬ Embeds K A ∧ ¬ Embeds I K

/-- Move the intermediate cardinal into the full coordinate type by its relational image. -/
theorem image_coordinate_bounds (A : α → Prop) (H : β → Prop) (I : γ → Prop)
    (L : β → β → Prop) (Q : β → β → β → Prop) (F : β → γ → Prop)
    (hw : WellOrderOn H L) (hq : PairingOn H Q) (hf : Injects F H I)
    (small : Embeds A H) (large : ¬ Embeds H A) (gap : ¬ Embeds I H) :
    CohenCoordinateBounds A I (RelImage F) (ImageOrder F L) (PairingImage F Q) := by
  have hb := injects_bijects_image H I F hf
  have forward : Embeds H (RelImage F) := ⟨F,hb.1⟩
  have backward : Embeds (RelImage F) H := ⟨fun y x => F x y,(bijects_inverse H (RelImage F) F hb).1⟩
  exact ⟨image_subset F H I hf.1,image_wellOrder F H I L hf hw,
    pairingImage_pairing H (RelImage F) F Q hb hq,
    embeds_trans A H (RelImage F) small forward,
    fun h => large (embeds_trans H (RelImage F) A forward h),
    fun h => gap (embeds_trans I (RelImage F) H h backward)⟩

/-- Eliminate the pairing and embedding witnesses before substituting high carrier types. -/
theorem coordinate_bounds_of_embeddings (A : α → Prop) (H : β → Prop) (I : γ → Prop)
    (L : β → β → Prop) (hw : WellOrderOn H L) (pairing : ∃ Q, PairingOn H Q)
    (small : Embeds A H) (large : ¬ Embeds H A) (embed : Embeds H I) (gap : ¬ Embeds I H) :
    ∃ K LK QK, CohenCoordinateBounds A I K LK QK := by
  obtain ⟨Q,hq⟩ := pairing
  obtain ⟨F,hf⟩ := embed
  exact ⟨RelImage F,ImageOrder F L,PairingImage F Q,
    image_coordinate_bounds A H I L Q F hw hq hf small large gap⟩

/-- General pairing construction before substituting a high-type Hartogs carrier. -/
theorem pairing_of_closedSegment_bounds (A : α → Prop) (H : β → Prop)
    (L : β → β → Prop) (Q : α → α → α → Prop)
    (hw : WellOrderOn H L) (hq : PairingOn A Q) (gap : ¬ Embeds H A)
    (closed : ∀ m, H m → Embeds (ClosedSegment H L m) A)
    (rcPair : Classicism.P.RigidComprehension (β → β → Prop)) :
    ∃ R, PairingOn H R :=
  pairing_of_pairCarrier_embedding H rcPair
    (wellOrder_embeds_from_segment_bounds A (PairCarrier H) (MaxPairOrder H L) H L
      (maxPairOrder_wellOrder H L hw) hw gap
      (maxPairOrder_segments_embed H L hw.1 A Q hq closed))

/-- The previously deferred closed-segment bound is an explicit premise here. -/
theorem hartogs_pairing_of_closedSegments (A : α → Prop)
    (rc : Classicism.P.RigidComprehension (OrdinalCarrier α → Prop))
    (rcPair : Classicism.P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (closed : ∀ m, HartogsCarrier A m →
      Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) m) A) :
    ∃ R, PairingOn (HartogsCarrier A) R :=
  pairing_of_closedSegment_bounds A (HartogsCarrier A) (HartogsOrder A) Q
    (hartogs_wellOrder rc A) hq (inductive_hartogs rc A).2.1 closed rcPair

theorem hartogs_coordinate_bounds (A : α → Prop) (L : α → α → Prop) (hw : WellOrderOn A L)
    (Q : α → α → α → Prop) (hq : PairingOn A Q)
    (rc1 : Classicism.P.RigidComprehension (OrdinalCarrier α → Prop))
    (rp1 : Classicism.P.RigidComprehension (OrdinalCarrier α → OrdinalCarrier α → Prop))
    (rc2 : Classicism.P.RigidComprehension (OrdinalCarrier (OrdinalCarrier α) → Prop))
    (closed : ∀ m, HartogsCarrier A m →
      Embeds (ClosedSegment (HartogsCarrier A) (HartogsOrder A) m) A) :
    ∃ K LK QK, CohenCoordinateBounds A (HartogsCarrier (HartogsCarrier A)) K LK QK :=
  coordinate_bounds_of_embeddings A (HartogsCarrier A) (HartogsCarrier (HartogsCarrier A))
    (HartogsOrder A) (hartogs_wellOrder rc1 A)
    (hartogs_pairing_of_closedSegments A rc1 rp1 Q hq closed)
    (wellOrder_embeds_hartogs rc1 A L hw) (inductive_hartogs rc1 A).2.1
    (wellOrder_embeds_hartogs rc2 (HartogsCarrier A) (HartogsOrder A) (hartogs_wellOrder rc1 A))
    (inductive_hartogs rc2 (HartogsCarrier A)).2.1

theorem natural_hartogs_coordinate_bounds {σ : Type} [Ty σ] (hp : LowerPeano σ)
    (rc1 : Classicism.P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rp1 : Classicism.P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rc2 : Classicism.P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((σ → Prop) → Prop)) → Prop))
    (closed : ∀ m, HartogsCarrier (@LowerNat σ _) m →
      Embeds (ClosedSegment (HartogsCarrier (@LowerNat σ _)) (HartogsOrder (@LowerNat σ _)) m) (@LowerNat σ _)) :
    ∃ K LK QK, CohenCoordinateBounds (@LowerNat σ _) (HartogsCarrier (HartogsCarrier (@LowerNat σ _))) K LK QK :=
  hartogs_coordinate_bounds LowerNat LowerLT (lowerNat_wellOrder hp) LowerPair (lowerPair_pairing hp)
    rc1 rp1 rc2 closed

#classicism_check image_coordinate_bounds coordinate_bounds_of_embeddings pairing_of_closedSegment_bounds hartogs_pairing_of_closedSegments hartogs_coordinate_bounds natural_hartogs_coordinate_bounds
#classicism_types image_coordinate_bounds coordinate_bounds_of_embeddings pairing_of_closedSegment_bounds hartogs_pairing_of_closedSegments hartogs_coordinate_bounds natural_hartogs_coordinate_bounds
end Classicism.MathematicalContingency
