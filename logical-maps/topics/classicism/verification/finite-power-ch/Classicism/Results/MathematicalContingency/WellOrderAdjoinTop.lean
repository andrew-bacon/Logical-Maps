import Classicism.Results.MathematicalContingency.OrdinalExistence

/-! Adjoin one fresh greatest element to a displayed well-order.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026.
No well-ordering principle, choice, rigidity, or infinity is assumed.
-/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def AdjoinTopCarrier (A : σ → Prop) (a : σ) : σ → Prop := fun x => A x ∨ x = a
def AdjoinTopOrder (A : σ → Prop) (R : σ → σ → Prop) (a : σ) : σ → σ → Prop :=
  fun x y => R x y ∨ (A x ∧ y = a)

theorem adjoinTop_wellOrder (A : σ → Prop) (R : σ → σ → Prop) (a : σ)
    (hw : WellOrderOn A R) (fresh : ¬ A a) :
    WellOrderOn (AdjoinTopCarrier A a) (AdjoinTopOrder A R a) := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro x y h
    exact h.elim (fun h => ⟨Or.inl (hw.1.1 x y h).1,Or.inl (hw.1.1 x y h).2⟩)
      (fun h => ⟨Or.inl h.1,Or.inr h.2⟩)
  · intro x _ h
    exact h.elim (fun h => hw.1.2.1 x (hw.1.1 x x h).1 h)
      (fun h => fresh (h.2 ▸ h.1))
  · intro x y z _ _ _ hxy hyz
    obtain hxy | hxy := hxy
    · obtain hyz | hyz := hyz
      · exact Or.inl (hw.1.2.2.1 x y z (hw.1.1 x y hxy).1
          (hw.1.1 x y hxy).2 (hw.1.1 y z hyz).2 hxy hyz)
      · exact Or.inr ⟨(hw.1.1 x y hxy).1,hyz.2⟩
    · have hy : A y := hyz.elim (fun h => (hw.1.1 y z h).1) And.left
      exact (fresh (hxy.2 ▸ hy)).elim
  · intro x y hx hy
    obtain hx | hx := hx
    · obtain hy | hy := hy
      · exact (hw.1.2.2.2 x y hx hy).elim Or.inl
          (fun h => Or.inr (h.elim (fun h => Or.inl (Or.inl h))
            (fun h => Or.inr (Or.inl h))))
      · exact Or.inr (Or.inl (Or.inr ⟨hx,hy⟩))
    · obtain hy | hy := hy
      · exact Or.inr (Or.inr (Or.inr ⟨hy,hx⟩))
      · exact Or.inl (hx.trans hy.symm)
  · intro Z sub inhabited
    obtain old | noOld := em (∃ x, Z x ∧ A x)
    · obtain ⟨x,hx,least⟩ := hw.2 (fun x => Z x ∧ A x) (fun _ h => h.2) old
      refine ⟨x,hx.1,?_⟩
      intro y hy h
      exact h.elim (fun h => least y ⟨hy,(hw.1.1 y x h).1⟩ h)
        (fun h => fresh (h.2 ▸ hx.2))
    · obtain ⟨x,hx⟩ := inhabited
      refine ⟨x,hx,?_⟩
      intro y hy h
      have ha : A y := h.elim (fun h => (hw.1.1 y x h).1) And.left
      exact noOld ⟨y,hy,ha⟩

theorem adjoinTop_segment_coext (A : σ → Prop) (R : σ → σ → Prop) (a : σ)
    (hw : WellOrderOn A R) (fresh : ¬ A a) :
    ∀ x, Segment (AdjoinTopCarrier A a) (AdjoinTopOrder A R a) a x ↔ A x := by
  intro x
  exact ⟨fun h => h.2.elim (fun h => (fresh (hw.1.1 x a h).2).elim) And.left,
    fun h => ⟨Or.inl h,Or.inr ⟨h,rfl⟩⟩⟩

theorem adjoinTop_segment_iso (A : σ → Prop) (R : σ → σ → Prop) (a : σ)
    (hw : WellOrderOn A R) (fresh : ¬ A a) :
    OrderIso (fun x y => A x ∧ x = y) A R
      (Segment (AdjoinTopCarrier A a) (AdjoinTopOrder A R a) a)
      (RestrictOrder (AdjoinTopOrder A R a)
        (Segment (AdjoinTopCarrier A a) (AdjoinTopOrder A R a) a)) := by
  have co := adjoinTop_segment_coext A R a hw fresh
  apply orderIso_of_coext _ _ _ _ (fun x => (co x).symm)
  intro x y hx hy
  exact ⟨fun h => ⟨(co x).mpr hx,(co y).mpr hy,Or.inl h⟩,
    fun h => h.2.2.elim (fun h => h) (fun h => (fresh (h.2 ▸ hy)).elim)⟩

#classicism_check adjoinTop_wellOrder adjoinTop_segment_coext adjoinTop_segment_iso
#classicism_types adjoinTop_wellOrder adjoinTop_segment_coext adjoinTop_segment_iso
end Classicism.MathematicalContingency
