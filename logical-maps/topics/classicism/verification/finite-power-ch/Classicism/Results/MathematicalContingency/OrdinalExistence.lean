import Classicism.Results.MathematicalContingency.OrdinalStructurality
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]
theorem orderIso_of_coext (A B : σ → Prop) (R S : σ → σ → Prop)
    (hc : ∀ x, A x ↔ B x) (hr : ∀ x y, A x → A y → (R x y ↔ S x y)) :
    OrderIso (fun x y => A x ∧ x = y) A R B S := by
  have hm : Maps (fun x y => A x ∧ x = y) A B :=
    ⟨fun x y h => ⟨h.1,h.2 ▸ (hc x).mp h.1⟩,
      fun x hx => ⟨x,(hc x).mp hx,hx,rfl⟩,fun _ _ _ h k => h.2.symm.trans k.2⟩
  refine ⟨⟨⟨hm,fun _ _ _ h k => h.2.trans k.2.symm⟩,hm,
    fun y hy => ⟨y,(hc y).mpr hy,(hc y).mpr hy,rfl⟩⟩,?_⟩
  intro x y u v hx hy
  exact hx.2 ▸ hy.2 ▸ hr x y hx.1 hy.1

theorem nested_segment_coext (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) (a b : σ) (ha : A a) (hb : Segment A R a b) :
    ∀ x, Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b x ↔ Segment A R b x := by
  intro x
  constructor
  · intro h; exact ⟨h.1.1,h.2.2.2⟩
  · intro h
    have hxa : Segment A R a x := ⟨h.1,hw.1.2.2.1 x b a h.1 hb.1 ha h.2 hb.2⟩
    exact ⟨hxa,hxa,hb,h.2⟩

theorem nested_segment_iso (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) (a b : σ) (ha : A a) (hb : Segment A R a b) :
    ∃ F, OrderIso F
      (Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b)
      (RestrictOrder (RestrictOrder R (Segment A R a))
        (Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b))
      (Segment A R b) (RestrictOrder R (Segment A R b)) := by
  let D := Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b
  have hc := nested_segment_coext A R hw a b ha hb
  refine ⟨fun x y => D x ∧ x = y,orderIso_of_coext _ _ _ _ hc ?_⟩
  intro x y hx hy
  exact ⟨fun h => ⟨(hc x).mp hx,(hc y).mp hy,h.2.2.2.2⟩,
    fun h => ⟨hx,hy,hx.1,hy.1,h.2.2⟩⟩

theorem ordinal_segment_flatten (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A : σ → Prop) (R : σ → σ → Prop) (hw : WellOrderOn A R)
    (a b : σ) (ha : A a) (hb : Segment A R a b)
    (h : α (RestrictOrder (RestrictOrder R (Segment A R a))
      (Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b))
      (Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b)) :
    α (RestrictOrder R (Segment A R b)) (Segment A R b) := by
  obtain ⟨F,hf⟩ := nested_segment_iso A R hw a b ha hb
  exact ordinal_iso_forward α hα _ _ _ _ F
    (wellOrder_restrict _ _ _ (wellOrder_restrict A _ R hw (fun _ hx => hx.1)) (fun _ hx => hx.1))
    (wellOrder_restrict A _ R hw (fun _ hx => hx.1)) hf h

theorem ordinal_no_self_successor (α : OrdinalCarrier σ) (hα : Ordinal α)
    (self : ∀ R A, α R A → OrdSuc α R A)
    (R : σ → σ → Prop) (A : σ → Prop) (hw : WellOrderOn A R) : ¬ α R A := by
  have hn : ∀ a, A a → ¬ α (RestrictOrder R (Segment A R a)) (Segment A R a) := by
    apply wellOrder_induction A R hw (fun a => ¬ α (RestrictOrder R (Segment A R a)) (Segment A R a))
    intro a ha ih h
    obtain ⟨b,hb,hβ⟩ := (self _ _ h).2
    exact ih b hb.1 hb.2 (ordinal_segment_flatten α hα A R hw a b ha hb hβ)
  intro h
  obtain ⟨a,ha,hβ⟩ := (self R A h).2
  exact hn a ha hβ

/-- RC supplies a rigid collection of successors realized by proper segments.
Its limit is exact; no rank function or uniqueness assumption is used. -/
theorem exact_ordinal_exists (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) (R : σ → σ → Prop) (hw : WellOrderOn A R) :
    ∃ α, Ordinal α ∧ ExactOrdinal α R A := by
  let Q : OrdinalCarrier σ → Prop := fun γ => ∃ β, Ordinal β ∧
    (∃ a, A a ∧ β (RestrictOrder R (Segment A R a)) (Segment A R a)) ∧ γ = OrdSuc β
  obtain ⟨Y,hy,hco⟩ := rc Q
  have hY : ∀ γ, Y γ → Ordinal γ := by
    intro γ hγ
    obtain ⟨β,hβ,_,he⟩ := (hco γ).mpr hγ
    exact he.symm ▸ ordinal_suc β hβ
  have hα : Ordinal (OrdLim Y) := ordinal_lim Y hy hY
  have hh : OrdLim Y R A := by
    refine ⟨hw,?_⟩
    intro γ hγ
    obtain ⟨β,hβ,ha,he⟩ := (hco γ).mpr hγ
    exact he.symm ▸ (show OrdSuc β R A from ⟨hw,ha⟩)
  refine ⟨OrdLim Y,hα,hh,?_⟩
  intro hs
  have hmem : Y (OrdSuc (OrdLim Y)) := (hco _).mp ⟨OrdLim Y,hα,hs.2,rfl⟩
  have self : ∀ S B, OrdLim Y S B → OrdSuc (OrdLim Y) S B := fun S B h => h.2 _ hmem
  exact ordinal_no_self_successor (OrdLim Y) hα self R A hw hh

#classicism_check orderIso_of_coext nested_segment_coext nested_segment_iso ordinal_segment_flatten
  ordinal_no_self_successor exact_ordinal_exists
#classicism_types orderIso_of_coext nested_segment_coext nested_segment_iso ordinal_segment_flatten
  ordinal_no_self_successor exact_ordinal_exists
end Classicism.MathematicalContingency
