import Classicism.Results.MathematicalContingency.ModalLemmas

/-! Mixed-type products represented by rigid singleton binary graphs.
This extends the existing same-type PairAt/PairCarrier convention definitionally.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def ProductPairAt (A : α → Prop) (B : β → Prop) (P : α → β → Prop) (x : α) (y : β) : Prop :=
  A x ∧ B y ∧ Rigid P ∧ ∀ u v, P u v ↔ u = x ∧ v = y

def RelProduct (A : α → Prop) (B : β → Prop) (P : α → β → Prop) : Prop :=
  ∃ x y, ProductPairAt A B P x y

theorem productPairAt_exists (A : α → Prop) (B : β → Prop)
    (rc : P.RigidComprehension (α → β → Prop))
    (x : α) (y : β) (hx : A x) (hy : B y) : ∃ P, ProductPairAt A B P x y := by
  obtain ⟨P,hP,e⟩ := rc (fun u v => u = x ∧ v = y)
  exact ⟨P,hx,hy,hP,fun u v => (e u v).symm⟩

theorem productPairAt_coordinates (A : α → Prop) (B : β → Prop)
    (P : α → β → Prop) (x u : α) (y v : β)
    (h : ProductPairAt A B P x y) (k : ProductPairAt A B P u v) : x = u ∧ y = v :=
  (k.2.2.2 x y).mp ((h.2.2.2 x y).mpr ⟨rfl,rfl⟩)

theorem productPairAt_unique (A : α → Prop) (B : β → Prop)
    (P Q : α → β → Prop) (x : α) (y : β)
    (h : ProductPairAt A B P x y) (k : ProductPairAt A B Q x y) : P = Q :=
  rigid_eq_of_coext P Q h.2.2.1 k.2.2.1
    (fun u v => (h.2.2.2 u v).trans (k.2.2.2 u v).symm)

#classicism_check productPairAt_exists productPairAt_coordinates productPairAt_unique
#classicism_types productPairAt_exists productPairAt_coordinates productPairAt_unique
end Classicism.MathematicalContingency
