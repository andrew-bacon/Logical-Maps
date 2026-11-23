import Classicism.Results.MathematicalContingency.RepresentativeFibres
import Classicism.Results.MathematicalContingency.CohenCounting
import Classicism.Results.MathematicalContingency.RigidPairs
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ α β γ : Type} [Ty σ] [Ty τ] [Ty α] [Ty β] [Ty γ]

theorem cohen_representativeImage_no_injection (hp : LowerPeano σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (E : (α → Prop) → Prop) (B : β → Prop) (L : β → β → Prop)
    (hw : WellOrderOn B L) (hb : Rigid B) (he : Rigid E)
    (rc : □ (Classicism.P.RigidComprehension (α → Prop)))
    (ic : Classicism.P.IntensionalChoice ((α → Prop) → β → Prop))
    (rcPair : Classicism.P.RigidComprehension (β → ((σ → Prop) → Prop) → Prop))
    (separate : ∀ X Y, E X → E Y → X ≠ Y → EntailmentOrder P (¬ (X ≡ Y)))
    (large : ¬ Embeds E (RelProduct B (@LowerNat σ _))) :
    EntailmentOrder P (¬ Embeds (RepresentativeImage E) B) :=
  representativeImage_no_injection E B P rc he ic separate
    (fun Q D below disjoint cover => cohen_cover_cardinality_obstruction hp I rcC LC H R o C
      hH hwC hc F P hf ho E B L D Q below disjoint hw hb cover rcPair large)

/-- A separated, currently uncountable frozen name carrier has no countable rigid image under P. -/
theorem cohen_intermediate_uncountable (hp : LowerPeano σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (E : (α → Prop) → Prop) (he : Rigid E) (rigidN : Rigid (@LowerNat σ _))
    (rc : □ (Classicism.P.RigidComprehension (α → Prop)))
    (ic : Classicism.P.IntensionalChoice ((α → Prop) → ((σ → Prop) → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop))
    (separate : ∀ X Y, E X → E Y → X ≠ Y → EntailmentOrder P (¬ (X ≡ Y)))
    (uncountable : ¬ Embeds E (@LowerNat σ _)) :
    EntailmentOrder P (¬ Embeds (RepresentativeImage E) (@LowerNat σ _)) :=
  cohen_representativeImage_no_injection hp I rcC LC H R o C hH hwC hc F P hf ho
    E LowerNat LowerLT (lowerNat_wellOrder hp) rigidN he rc ic rcPair separate
    (fun h => uncountable (embeds_trans E (RelProduct LowerNat LowerNat) LowerNat h
      (pairCarrier_embedding_of_pairing LowerNat LowerPair (lowerPair_pairing hp))))

#classicism_check cohen_representativeImage_no_injection cohen_intermediate_uncountable
#classicism_types cohen_representativeImage_no_injection cohen_intermediate_uncountable
end Classicism.MathematicalContingency
