import Classicism.Results.MathematicalContingency.IndexedNames
import Classicism.Results.MathematicalContingency.CarrierTheory
import Classicism.Results.MathematicalContingency.RepresentativeFibres
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α τ β : Type} [Ty α] [Ty τ] [Ty β]

theorem nameCarrier_subsets (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (X : α → Prop) (hx : NameCarrier A I T X) : □ (∀ a, X a → A a) :=
  hx.elim (fun _ h => h.2.1)

/-- Separation indexed by distinct coordinates also separates distinct current names. -/
theorem nameCarrier_separation (A : α → Prop) (I : τ → Prop) (T : τ → α → Prop → Prop)
    (P : Prop) (ha : Rigid A) (total : ∀ a n, I a → A n → ∃ p, T a n p)
    (separate : ∀ a b X Y, IndexedName A I T a X → IndexedName A I T b Y →
      a ≠ b → EntailmentOrder P (¬ (X ≡ Y)))
    (X Y : α → Prop) (hx : NameCarrier A I T X) (hy : NameCarrier A I T Y) (hn : X ≠ Y) :
    EntailmentOrder P (¬ (X ≡ Y)) := by
  obtain ⟨a,haX⟩ := hx
  obtain ⟨b,hbY⟩ := hy
  exact separate a b X Y haX hbY (fun e =>
    hn (indexedName_unique A I T ha total a X Y haX (e.symm ▸ hbY)))

/-- Restricting the coordinate carrier restricts its relational name bijection. -/
theorem indexedName_subfamily_bijects (A : α → Prop) (I K : τ → Prop)
    (T : τ → α → Prop → Prop) (sub : ∀ a, K a → I a)
    (h : Bijects (IndexedName A I T) I (NameCarrier A I T)) :
    Bijects (IndexedName A K T) K (NameCarrier A K T) := by
  have hm : Maps (IndexedName A K T) K (NameCarrier A K T) := by
    refine ⟨fun a X hx => ⟨hx.1,a,hx⟩,?_,?_⟩
    · intro a ha
      obtain ⟨X,_,hx⟩ := h.1.1.2.1 a (sub a ha)
      exact ⟨X,⟨a,ha,hx.2⟩,ha,hx.2⟩
    · intro a X Y hx hy
      exact h.1.1.2.2 a X Y ⟨sub a hx.1,hx.2⟩ ⟨sub a hy.1,hy.2⟩
  exact ⟨⟨hm,fun a b X hx hy => h.1.2 a b X ⟨sub a hx.1,hx.2⟩ ⟨sub b hy.1,hy.2⟩⟩,
    hm,fun X hx => hx.elim (fun a ha => ⟨a,ha.1,ha⟩)⟩

/-- Current coextension suffices to transfer a lower cardinal bound to a frozen carrier. -/
theorem frozenNameCarrier_not_embeds (A : α → Prop) (I : τ → Prop)
    (T : τ → α → Prop → Prop) (E : (α → Prop) → Prop) (B : β → Prop)
    (h : Bijects (IndexedName A I T) I (NameCarrier A I T))
    (he : E ≡ NameCarrier A I T) (large : ¬ Embeds I B) : ¬ Embeds E B :=
  fun k => large (embeds_trans I E B
    (embeds_trans I (NameCarrier A I T) E ⟨IndexedName A I T,h.1⟩
      (embeds_of_subset (NameCarrier A I T) E (fun X hx => (he X).mpr hx))) k)

/-- A frozen collection of names for subsets yields only rigid subsets at every world. -/
theorem representativeImage_rigidPower (A : α → Prop) (E : (α → Prop) → Prop)
    (he : Rigid E) (subsets : ∀ X, E X → □ (∀ a, X a → A a)) :
    □ (∀ U, RepresentativeImage E U → RigidPower A U) :=
  modal_K _ _ (nec% (fun (h : ∀ X, E X → ∀ a, X a → A a)
    U (hu : RepresentativeImage E U) =>
    (show RigidPower A U from ⟨hu.1,fun a ha => hu.2.elim
      (fun X hx => h X hx.1 a ((hx.2 a).mp ha))⟩)))
    (restricted_barcan_unary E (fun X => ∀ a, X a → A a) he subsets)

#classicism_check nameCarrier_subsets nameCarrier_separation indexedName_subfamily_bijects frozenNameCarrier_not_embeds representativeImage_rigidPower
#classicism_types nameCarrier_subsets nameCarrier_separation indexedName_subfamily_bijects frozenNameCarrier_not_embeds representativeImage_rigidPower
end Classicism.MathematicalContingency
