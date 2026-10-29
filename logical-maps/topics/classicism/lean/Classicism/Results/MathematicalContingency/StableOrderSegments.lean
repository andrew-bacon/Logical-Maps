import Classicism.Results.MathematicalContingency.StableWellOrder

/-! Stable well-orders and their segments, for induction on order-type properties.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

/-- Only current weak rigidity and stability on current members are needed. -/
def StableOrder (A : σ → Prop) (R : σ → σ → Prop) : Prop :=
  □ (WellOrderOn A R) ∧ WeaklyRigid A ∧
    ∀ x y, A x → A y → □ (R x y) ∨ □ (¬ R x y)

theorem rigid_wellOrder_stable (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) (ha : Rigid A) (hr : Rigid R) (nd : DomainND A) :
    StableOrder A R :=
  ⟨rigid_wellOrder_necessary A R hw ha hr nd, weaklyRigid_of_rigid ha,
    fun x y hx hy => rigid_binary_atomic A A R nd nd hr hw.1.1 x y hx hy⟩

/-- Order-specific instance of upstream RigidityClosure.weak_cut.
The standalone snapshot lacks that research module; this proof specializes its argument. -/
theorem stable_segment_weaklyRigid (A : σ → Prop) (R : σ → σ → Prop)
    (h : StableOrder A R) (a : σ) (ha : A a) : WeaklyRigid (Segment A R a) := by
  constructor
  · intro x hx
    obtain hp | hn := h.2.2 x a hx.1 ha
    · exact modal_K _ _ (modal_K _ _
        (nec% (fun (hax : A x) (hr : R x a) => (show Segment A R a x from ⟨hax,hr⟩)))
        (h.2.1.1 x hx.1)) hp
    · exact (box_elim hn hx.2).elim
  · intro X hX
    have hb : □ (∀ x, A x → R x a → X x) := h.2.1.2 (fun x => R x a → X x) (by
      intro x hx
      obtain hp | hn := h.2.2 x a hx ha
      · exact box_imp_of_box _ _ (hX x ⟨hx,box_elim hp⟩)
      · exact box_imp_of_box_not _ _ hn)
    exact modal_K _ _ (nec% (fun (hb : ∀ x, A x → R x a → X x)
      x (hx : Segment A R a x) => hb x hx.1 hx.2)) hb

theorem stableOrder_segment (A : σ → Prop) (R : σ → σ → Prop)
    (h : StableOrder A R) (a : σ) (ha : A a) :
    StableOrder (Segment A R a) (RestrictOrder R (Segment A R a)) := by
  have hs := stable_segment_weaklyRigid A R h a ha
  refine ⟨modal_K _ _ (nec% (fun (hw : WellOrderOn A R) =>
    wellOrder_restrict A (Segment A R a) R hw (fun x hx => hx.1))) h.1,hs,?_⟩
  intro x y hx hy
  obtain hp | hn := h.2.2 x y hx.1 hy.1
  · exact Or.inl (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (hx : Segment A R a x) (hy : Segment A R a y) (hr : R x y) =>
        (show RestrictOrder R (Segment A R a) x y from ⟨hx,hy,hr⟩)))
      (hs.1 x hx)) (hs.1 y hy)) hp)
  · exact Or.inr (modal_K _ _ (nec% (fun (hn : ¬ R x y)
      (hr : RestrictOrder R (Segment A R a) x y) => hn hr.2.2)) hn)

#classicism_check rigid_wellOrder_stable stable_segment_weaklyRigid stableOrder_segment
#classicism_types rigid_wellOrder_stable stable_segment_weaklyRigid stableOrder_segment
end Classicism.MathematicalContingency
