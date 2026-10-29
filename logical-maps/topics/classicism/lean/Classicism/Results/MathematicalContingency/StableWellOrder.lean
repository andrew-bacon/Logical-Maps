import Classicism.Results.MathematicalContingency.StableStrictOrder
import Classicism.Results.MathematicalContingency.CarrierTheory

/-! Well-foundedness transport without a global Barcan principle.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α : Type} [Ty α]

theorem stable_wellOrder_induction (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (ha : Rigid A)
    (negative : ∀ x y, A x → A y → ¬ L x y → □ (¬ L x y))
    (P : α → Prop)
    (step : □ (∀ x, A x → (∀ y, A y → L y x → P y) → P x)) : □ (∀ x, A x → P x) := by
  apply restricted_barcan_unary A P ha
  apply wellOrder_induction A L hw (fun x => □ (P x))
  intro x hx ih
  have pred : □ (∀ y, A y → L y x → P y) :=
    restricted_barcan_unary A (fun y => L y x → P y) ha (by
      intro y hy
      obtain h | h := em (L y x)
      · exact box_imp_of_box _ _ (ih y hy h)
      · exact box_imp_of_box_not _ _ (negative y x hy hx h))
  exact modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (hs : ∀ x, A x → (∀ y, A y → L y x → P y) → P x)
      (hax : A x) (hp : ∀ y, A y → L y x → P y) => hs x hax hp)) step)
      (box_elim ha.1 x hx)) pred

def WellFoundedBelow (A : α → Prop) (L : α → α → Prop) (a : α) : Prop :=
  ∀ X : α → Prop, (∀ x, X x → A x ∧ L x a) → (∃ x, X x) →
    ∃ x, X x ∧ ∀ y, X y → ¬ L y x

theorem wellFoundedBelow_step (A : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (a : α) (ha : A a)
    (ih : ∀ b, A b → L b a → WellFoundedBelow A L b) : WellFoundedBelow A L a := by
  intro X hX he
  obtain ⟨b,hb⟩ := he
  obtain h | h := em (∃ y, X y ∧ L y b)
  · obtain ⟨c,hc,hm⟩ := ih b (hX b hb).1 (hX b hb).2
      (fun y => X y ∧ L y b) (fun y hy => ⟨(hX y hy.1).1,hy.2⟩) h
    exact ⟨c,hc.1,fun y hy hyc => hm y ⟨hy,hl.2.2.1 y c b
      (hX y hy).1 (hX c hc.1).1 (hX b hb).1 hyc hc.2⟩ hyc⟩
  · exact ⟨b,hb,fun y hy hyb => h ⟨y,hy,hyb⟩⟩

theorem wellOrder_of_wellFoundedBelow (A : α → Prop) (L : α → α → Prop)
    (hl : StrictOrderOn A L) (hf : ∀ a, A a → WellFoundedBelow A L a) : WellOrderOn A L := by
  refine ⟨hl,?_⟩
  intro X hX he
  obtain ⟨b,hb⟩ := he
  obtain h | h := em (∃ y, X y ∧ L y b)
  · obtain ⟨c,hc,hm⟩ := hf b (hX b hb)
      (fun y => X y ∧ L y b) (fun y hy => ⟨hX y hy.1,hy.2⟩) h
    exact ⟨c,hc.1,fun y hy hyc => hm y ⟨hy,hl.2.2.1 y c b
      (hX y hy) (hX c hc.1) (hX b hb) hyc hc.2⟩ hyc⟩
  · exact ⟨b,hb,fun y hy hyb => h ⟨y,hy,hyb⟩⟩

theorem necessary_wellOrder_of_atomic_stability (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (ha : Rigid A)
    (negative : ∀ x y, A x → A y → ¬ L x y → □ (¬ L x y))
    (hs : □ (StrictOrderOn A L)) : □ (WellOrderOn A L) := by
  have step : □ (∀ x, A x → (∀ y, A y → L y x → WellFoundedBelow A L y) → WellFoundedBelow A L x) :=
    modal_K _ _ (nec% (wellFoundedBelow_step A L)) hs
  have hf := stable_wellOrder_induction A L hw ha negative (WellFoundedBelow A L) step
  exact modal_K _ _ (modal_K _ _ (nec% (wellOrder_of_wellFoundedBelow A L)) hs) hf

theorem rigid_wellOrder_necessary (A : α → Prop) (L : α → α → Prop)
    (hw : WellOrderOn A L) (ha : Rigid A) (hl : Rigid L) (nd : DomainND A)
    : □ (WellOrderOn A L) :=
  necessary_wellOrder_of_atomic_stability A L hw ha
    (rigid_binary_negative A A L nd nd hl hw.1.1)
    (rigid_strictOrder_necessary A L ha hl nd hw.1)

#classicism_check stable_wellOrder_induction wellFoundedBelow_step wellOrder_of_wellFoundedBelow necessary_wellOrder_of_atomic_stability rigid_wellOrder_necessary
#classicism_types stable_wellOrder_induction wellFoundedBelow_step wellOrder_of_wellFoundedBelow necessary_wellOrder_of_atomic_stability rigid_wellOrder_necessary
end Classicism.MathematicalContingency
