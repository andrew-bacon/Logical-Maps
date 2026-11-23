import Classicism.Results.MathematicalContingency.WellOrderCardinality
import Classicism.Results.MathematicalContingency.HartogsTheorem
import Classicism.Results.MathematicalContingency.NaturalWellOrder

/-! Two Hartogs stages and a common carrier for I1 and I2.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem wellOrder_hartogs_segment (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) (L : σ → σ → Prop) (hw : WellOrderOn A L) :
    ∃ a, HartogsCarrier A a ∧ ∃ F, OrderIso F A L
      (Segment (HartogsCarrier A) (HartogsOrder A) a)
      (RestrictOrder (HartogsOrder A) (Segment (HartogsCarrier A) (HartogsOrder A) a)) := by
  exact wellOrder_proper_segment_of_not_embeds A L (HartogsCarrier A) (HartogsOrder A)
    hw (hartogs_wellOrder rc A) (inductive_hartogs rc A).2.1

theorem wellOrder_embeds_hartogs (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) (L : σ → σ → Prop) (hw : WellOrderOn A L) : Embeds A (HartogsCarrier A) := by
  exact wellOrder_embeds_of_not_embeds A L (HartogsCarrier A) (HartogsOrder A)
    hw (hartogs_wellOrder rc A) (inductive_hartogs rc A).2.1

theorem wellOrder_smaller_hartogs (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) (L : σ → σ → Prop) (hw : WellOrderOn A L) : Smaller A (HartogsCarrier A) :=
  ⟨wellOrder_embeds_hartogs rc A L hw,(inductive_hartogs rc A).2.1⟩

def DoubleHartogsIndices (A : σ → Prop)
    (I1 I2 : OrdinalCarrier (OrdinalCarrier σ) → Prop)
    (L : OrdinalCarrier (OrdinalCarrier σ) → OrdinalCarrier (OrdinalCarrier σ) → Prop) : Prop :=
  (∀ x, I1 x → I2 x) ∧ WellOrderOn I1 (RestrictOrder L I1) ∧ WellOrderOn I2 L ∧
  Smaller A I1 ∧ Smaller I1 I2 ∧ Equinumerous I1 (HartogsCarrier A) ∧
  ∀ x, I2 x → Embeds (Segment I2 L x) I1

theorem doubleHartogs_indices
    (rc1 : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier σ) → Prop))
    (A : σ → Prop) (L : σ → σ → Prop) (hw : WellOrderOn A L) :
    ∃ I1, DoubleHartogsIndices A I1 (HartogsCarrier (HartogsCarrier A))
      (HartogsOrder (HartogsCarrier A)) := by
  let H := HartogsCarrier A
  let J := HartogsCarrier H
  let S := HartogsOrder H
  have wh := hartogs_wellOrder rc1 A
  have wj := hartogs_wellOrder rc2 H
  obtain ⟨a,ha,F,hF⟩ := wellOrder_hartogs_segment rc2 H (HartogsOrder A) wh
  let I := Segment J S a
  have forward : Embeds H I := ⟨F,hF.1.1⟩
  have inverse := orderIso_inverse H I (HartogsOrder A) (RestrictOrder S I) F hF
  have backward : Embeds I H := ⟨fun x y => F y x,inverse.1.1⟩
  have sub : ∀ x, I x → J x := fun _ h => h.1
  refine ⟨I,sub,wellOrder_restrict J I S wj sub,wj,?_,?_,⟨_,inverse.1⟩,?_⟩
  · exact ⟨embeds_trans A H I (wellOrder_embeds_hartogs rc1 A L hw) forward,
      fun h => (inductive_hartogs rc1 A).2.1 (embeds_trans H I A forward h)⟩
  · exact ⟨embeds_of_subset I J sub,(hartogs_initialCardinal rc2 H).2 a ha⟩
  · intro x hx
    exact embeds_trans _ H I (hartogs_segment_embeds H x hx) forward

theorem natural_hartogs_indices (hp : LowerPeano σ)
    (rc1 : P.RigidComprehension (OrdinalCarrier ((σ → Prop) → Prop) → Prop))
    (rc2 : P.RigidComprehension (OrdinalCarrier (OrdinalCarrier ((σ → Prop) → Prop)) → Prop)) :
    ∃ I1, DoubleHartogsIndices (@LowerNat σ _) I1 (HartogsCarrier (HartogsCarrier (@LowerNat σ _)))
      (HartogsOrder (HartogsCarrier (@LowerNat σ _))) :=
  doubleHartogs_indices rc1 rc2 LowerNat LowerLT (lowerNat_wellOrder hp)

#classicism_check wellOrder_hartogs_segment wellOrder_embeds_hartogs wellOrder_smaller_hartogs doubleHartogs_indices natural_hartogs_indices
#classicism_types wellOrder_hartogs_segment wellOrder_embeds_hartogs wellOrder_smaller_hartogs doubleHartogs_indices natural_hartogs_indices
end Classicism.MathematicalContingency
