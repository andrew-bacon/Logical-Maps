import Classicism.Results.MathematicalContingency.ModalLemmas

/-! Atomic stability of rigid relations on necessarily distinct domains.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {α β : Type} [Ty α] [Ty β]

def DomainND (A : α → Prop) : Prop := ∀ x y, A x → A y → x ≠ y → □ (x ≠ y)

theorem rigid_subset_negative (A X : α → Prop) (nd : DomainND A) (hr : Rigid X)
    (sub : ∀ x, X x → A x) (x : α) (hx : A x) (hn : ¬ X x) : □ (¬ X x) := by
  have h : □ (∀ y, X y → y ≠ x) := restricted_barcan_unary X (fun y => y ≠ x) hr
    (fun y hy => nd y x (sub y hy) hx (fun e => hn (e ▸ hy)))
  exact modal_K _ _ (nec% (fun (h : ∀ y, X y → y ≠ x) (hX : X x) => h x hX rfl)) h

theorem rigid_subset_atomic (A X : α → Prop) (nd : DomainND A) (hr : Rigid X)
    (sub : ∀ x, X x → A x) (x : α) (hx : A x) : □ (X x) ∨ □ (¬ X x) :=
  (em (X x)).elim (fun h => Or.inl (box_elim hr.1 x h))
    (fun h => Or.inr (rigid_subset_negative A X nd hr sub x hx h))

theorem rigidPower_nd (A : α → Prop) (nd : DomainND A) : DomainND (RigidPower A) := by
  intro X Y hx hy hne
  have witness : (∃ x, X x ∧ ¬ Y x) ∨ ∃ x, Y x ∧ ¬ X x := by
    obtain h | h := em (∃ x, X x ∧ ¬ Y x)
    · exact Or.inl h
    · obtain k | k := em (∃ x, Y x ∧ ¬ X x)
      · exact Or.inr k
      · exact (hne (rigid_eq_of_coext X Y hx.1 hy.1 (fun x =>
          ⟨fun hX => (em (Y x)).elim id (fun hn => (h ⟨x,hX,hn⟩).elim),
           fun hY => (em (X x)).elim id (fun hn => (k ⟨x,hY,hn⟩).elim)⟩))).elim
  obtain ⟨x,hX,hnY⟩ | ⟨x,hY,hnX⟩ := witness
  · exact modal_K _ _ (modal_K _ _
      (nec% (fun (hX : X x) (hnY : ¬ Y x) (e : X = Y) => hnY (e ▸ hX)))
      (box_elim hx.1.1 x hX)) (rigid_subset_negative A Y nd hy.1 hy.2 x (hx.2 x hX) hnY)
  · exact modal_K _ _ (modal_K _ _
      (nec% (fun (hY : Y x) (hnX : ¬ X x) (e : X = Y) => hnX (e.symm ▸ hY)))
      (box_elim hy.1.1 x hY)) (rigid_subset_negative A X nd hx.1 hx.2 x (hy.2 x hY) hnX)

theorem rigid_binary_negative (A : α → Prop) (B : β → Prop) (R : α → β → Prop)
    (ndA : DomainND A) (ndB : DomainND B) (hr : Rigid R)
    (sub : ∀ x y, R x y → A x ∧ B y) (x : α) (y : β) (hx : A x) (hy : B y)
    (hn : ¬ R x y) : □ (¬ R x y) := by
  have h : □ (∀ u v, R u v → u ≠ x ∨ v ≠ y) :=
    restricted_barcan R (fun u v => u ≠ x ∨ v ≠ y) hr.2 (by
      intro u v huv
      obtain e | e := em (u = x)
      · subst u
        have hv : v ≠ y := fun e => hn (e ▸ huv)
        exact modal_K _ _ (nec% (fun (h : v ≠ y) => (Or.inr h : x ≠ x ∨ v ≠ y)))
          (ndB v y (sub x v huv).2 hy hv)
      · exact modal_K _ _ (nec% (fun (h : u ≠ x) => (Or.inl h : u ≠ x ∨ v ≠ y)))
          (ndA u x (sub u v huv).1 hx e))
  exact modal_K _ _ (nec% (fun (h : ∀ u v, R u v → u ≠ x ∨ v ≠ y) (hR : R x y) =>
    (h x y hR).elim (fun e => e rfl) (fun e => e rfl))) h

theorem rigid_binary_atomic (A : α → Prop) (B : β → Prop) (R : α → β → Prop)
    (ndA : DomainND A) (ndB : DomainND B) (hr : Rigid R)
    (sub : ∀ x y, R x y → A x ∧ B y) (x : α) (y : β) (hx : A x) (hy : B y) :
    □ (R x y) ∨ □ (¬ R x y) :=
  (em (R x y)).elim (fun h => Or.inl (box_elim hr.1 x y h))
    (fun h => Or.inr (rigid_binary_negative A B R ndA ndB hr sub x y hx hy h))

#classicism_check rigid_subset_negative rigid_subset_atomic rigidPower_nd rigid_binary_negative rigid_binary_atomic
#classicism_types rigid_subset_negative rigid_subset_atomic rigidPower_nd rigid_binary_negative rigid_binary_atomic
end Classicism.MathematicalContingency
