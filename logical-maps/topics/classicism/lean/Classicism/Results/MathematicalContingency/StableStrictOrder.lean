import Classicism.Results.MathematicalContingency.StableTransport

/-! Transport of current strict-order laws over a rigid ND domain.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

theorem rigid_forall_two (A : α → Prop) (ha : Rigid A) (P : α → α → Prop)
    (h : ∀ x y, A x → A y → □ (P x y)) : □ (∀ x, A x → ∀ y, A y → P x y) :=
  restricted_barcan_unary A (fun x => ∀ y, A y → P x y) ha
    (fun x hx => restricted_barcan_unary A (P x) ha (fun y hy => h x y hx hy))

theorem rigid_forall_three (A : α → Prop) (ha : Rigid A) (P : α → α → α → Prop)
    (h : ∀ x y z, A x → A y → A z → □ (P x y z)) :
    □ (∀ x, A x → ∀ y, A y → ∀ z, A z → P x y z) :=
  rigid_forall_two A ha (fun x y => ∀ z, A z → P x y z)
    (fun x y hx hy => restricted_barcan_unary A (P x y) ha (fun z hz => h x y z hx hy hz))

theorem rigid_strictOrder_domain (A : α → Prop) (L : α → α → Prop)
    (ha : Rigid A) (hl : Rigid L) (hs : StrictOrderOn A L) :
    □ (∀ x y, L x y → A x ∧ A y) :=
  restricted_barcan L (fun x y => A x ∧ A y) hl.2
    (fun x y h => modal_K _ _ (modal_K _ _
      (nec% (fun (hx : A x) (hy : A y) => And.intro hx hy))
      (box_elim ha.1 x (hs.1 x y h).1)) (box_elim ha.1 y (hs.1 x y h).2))

theorem rigid_strictOrder_trans (A : α → Prop) (L : α → α → Prop)
    (ha : Rigid A) (hl : Rigid L) (nd : DomainND A) (hs : StrictOrderOn A L) :
    □ (∀ x y z, A x → A y → A z → L x y → L y z → L x z) := by
  have h := rigid_forall_three A ha (fun x y z => L x y → L y z → L x z) (by
    intro x y z hx hy hz
    obtain hxy | hxy := em (L x y)
    · obtain hyz | hyz := em (L y z)
      · exact box_imp_of_box _ _ (box_imp_of_box _ _
          (box_elim hl.1 x z (hs.2.2.1 x y z hx hy hz hxy hyz)))
      · exact box_imp_of_box _ _ (box_imp_of_box_not _ _
          (rigid_binary_negative A A L nd nd hl hs.1 y z hy hz hyz))
    · exact box_imp_of_box_not _ _ (rigid_binary_negative A A L nd nd hl hs.1 x y hx hy hxy))
  exact modal_K _ _ (nec% (fun
    (h : ∀ x, A x → ∀ y, A y → ∀ z, A z → L x y → L y z → L x z)
    x y z hx hy hz => h x hx y hy z hz)) h

theorem rigid_strictOrder_total (A : α → Prop) (L : α → α → Prop)
    (ha : Rigid A) (hl : Rigid L) (hs : StrictOrderOn A L) :
    □ (∀ x y, A x → A y → x = y ∨ L x y ∨ L y x) := by
  have h := rigid_forall_two A ha (fun x y => x = y ∨ L x y ∨ L y x) (by
    intro x y hx hy
    obtain e | h | h := hs.2.2.2 x y hx hy
    · exact modal_K _ _ (nec% (fun (e : x = y) => (Or.inl e : x = y ∨ L x y ∨ L y x)))
        (necessity_of_identity x y e)
    · exact modal_K _ _ (nec% (fun (h : L x y) => (Or.inr (Or.inl h) : x = y ∨ L x y ∨ L y x)))
        (box_elim hl.1 x y h)
    · exact modal_K _ _ (nec% (fun (h : L y x) => (Or.inr (Or.inr h) : x = y ∨ L x y ∨ L y x)))
        (box_elim hl.1 y x h))
  exact modal_K _ _ (nec% (fun (h : ∀ x, A x → ∀ y, A y → x = y ∨ L x y ∨ L y x)
    x y hx hy => h x hx y hy)) h

theorem rigid_strictOrder_necessary (A : α → Prop) (L : α → α → Prop)
    (ha : Rigid A) (hl : Rigid L) (nd : DomainND A) (hs : StrictOrderOn A L) :
    □ (StrictOrderOn A L) := by
  have hi : □ (∀ x, A x → ¬ L x x) := restricted_barcan_unary A (fun x => ¬ L x x) ha
    (fun x hx => rigid_binary_negative A A L nd nd hl hs.1 x x hx hx (hs.2.1 x hx))
  exact modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hd : ∀ x y, L x y → A x ∧ A y) (hi : ∀ x, A x → ¬ L x x)
      (ht : ∀ x y z, A x → A y → A z → L x y → L y z → L x z)
      (hc : ∀ x y, A x → A y → x = y ∨ L x y ∨ L y x) =>
        (show StrictOrderOn A L from ⟨hd,hi,ht,hc⟩)))
      (rigid_strictOrder_domain A L ha hl hs)) hi)
      (rigid_strictOrder_trans A L ha hl nd hs)) (rigid_strictOrder_total A L ha hl hs)

#classicism_check rigid_forall_two rigid_forall_three rigid_strictOrder_domain rigid_strictOrder_trans rigid_strictOrder_total rigid_strictOrder_necessary
#classicism_types rigid_forall_two rigid_forall_three rigid_strictOrder_domain rigid_strictOrder_trans rigid_strictOrder_total rigid_strictOrder_necessary
end Classicism.MathematicalContingency
