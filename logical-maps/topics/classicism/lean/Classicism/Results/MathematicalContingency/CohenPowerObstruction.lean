import Classicism.Results.MathematicalContingency.PowerRepresentativeFibres
import Classicism.Results.MathematicalContingency.CohenCounting
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {σ τ α β γ : Type} [Ty σ] [Ty τ] [Ty α] [Ty β] [Ty γ]

/-- The second modal obstruction, conditional on the current cardinal gap D > E times N. -/
theorem cohen_rigidPower_no_injection (hp : LowerPeano σ) (I : τ → Prop)
    (rcC : Classicism.P.RigidComprehension (CohenGraph σ τ))
    (LC : CohenGraph σ τ → CohenGraph σ τ → Prop)
    (H : γ → Prop) (R : γ → γ → Prop) (o : γ) (C : CohenGraph σ τ → γ → Prop)
    (hH : PartialOrderOn H R) (hwC : WellOrderOn (CohenCondition I) LC)
    (hc : DenseCones (CohenCondition I) (ConditionOrder LowerNat I ConditionBit) H R o C)
    (F : γ → Prop → Prop) (P : Prop)
    (hf : OrderIso F H R (Below P) EntailmentOrder) (ho : F o False)
    (A : α → Prop) (D : (α → Prop) → Prop) (E : (β → Prop) → Prop)
    (L : (β → Prop) → (β → Prop) → Prop) (hw : WellOrderOn E L) (he : Rigid E)
    (rc : □ (Classicism.P.RigidComprehension (α → Prop)))
    (ic : Classicism.P.IntensionalChoice ((α → Prop) → (β → Prop) → Prop))
    (rcPair : Classicism.P.RigidComprehension ((β → Prop) → ((σ → Prop) → Prop) → Prop))
    (subsets : ∀ X, D X → EntailmentOrder P (∀ a, X a → A a))
    (separate : ∀ X Z, D X → D Z → X ≠ Z → EntailmentOrder P (¬ (X ≡ Z)))
    (large : ¬ Embeds D (RelProduct E (@LowerNat σ _))) :
    EntailmentOrder P (¬ Embeds (RigidPower A) (RepresentativeImage E)) :=
  rigidPower_representativeImage_no_injection A D E P rc ic subsets separate
    (fun Q V below disjoint cover => cohen_cover_cardinality_obstruction hp I rcC LC H R o C
      hH hwC hc F P hf ho D E L V Q below disjoint hw he cover rcPair large)

#classicism_check cohen_rigidPower_no_injection
#classicism_types cohen_rigidPower_no_injection
end Classicism.MathematicalContingency
