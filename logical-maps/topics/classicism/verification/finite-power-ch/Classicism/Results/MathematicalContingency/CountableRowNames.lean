import Classicism.Results.MathematicalContingency.CountableCoordinateLaws
import Classicism.Results.MathematicalContingency.FrozenNameCarriers
namespace Classicism.MathematicalContingency
variable {σ τ β : Type} [Ty σ] [Ty τ] [Ty β]

theorem countable_names_maps (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (T : τ → ((σ → Prop) → Prop) → Prop → Prop) (rigidN : Rigid (@LowerNat σ _))
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop))
    (total : ∀ a n, I a → LowerNat n → ∃ p, T a n p)
    (functional : ∀ a n p q, I a → LowerNat n → T a n p → T a n q → p = q) :
    Maps (IndexedName LowerNat I T) I (NameCarrier LowerNat I T) :=
  indexedName_maps LowerNat I T rigidN total
    (indexedName_exists LowerNat I T rc rigidN (lowerNat_nd hi) total functional)

theorem countableCoordinate_names_maps (hi : DraftBoxInfinity σ) (I : τ → Prop)
    (B : β → Prop) (R : β → β → Prop) (C : CountableBitGraph σ τ → β → Prop)
    (cba : CBA B R) (maps : Maps C (CountableBitCarrier I) B)
    (F : β → Prop → Prop) (P : Prop) (fmap : Maps F B (Below P))
    (rigidN : Rigid (@LowerNat σ _))
    (rc : Classicism.P.RigidComprehension (((σ → Prop) → Prop) → Prop → Prop)) :
    Maps (IndexedName LowerNat I (CountableCoordinateValue I B R C F)) I
      (NameCarrier LowerNat I (CountableCoordinateValue I B R C F)) :=
  countable_names_maps hi I (CountableCoordinateValue I B R C F) rigidN rc
    (fun a n _ _ => countableCoordinateValue_total I B R C cba.2.1 maps F P fmap a n)
    (fun a n p q _ _ => countableCoordinateValue_functional I B R C cba.1 F P fmap a n p q)

#classicism_check countable_names_maps countableCoordinate_names_maps
#classicism_types countable_names_maps countableCoordinate_names_maps
end Classicism.MathematicalContingency
