import Classicism.Results.MathematicalContingency.WellOrderComparison
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
theorem initial_order_iff (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hf : InitialEmbedding F A R B S) :
    ∀ x y u v, F x u → F y v → (R x y ↔ S u v) := by
  intro x y u v hx hy
  refine ⟨hf.1.2 x y u v hx hy,?_⟩
  intro huv
  obtain ⟨w,hwy,hwu⟩ := hf.2 y v u hy (hf.1.1.1.1 x u hx).2 huv
  exact (hf.1.1.2 w x u hwu hx) ▸ hwy

theorem initial_embedding_classification (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hs : WellOrderOn B S) (hf : InitialEmbedding F A R B S) :
    OrderIso F A R B S ∨ ∃ b, B b ∧ OrderIso F A R (Segment B S b) (RestrictOrder S (Segment B S b)) := by
  refine (em (∀ y, B y → ∃ x, F x y)).elim ?_ ?_
  · intro hfull
    exact Or.inl ⟨⟨hf.1.1,hf.1.1.1,fun y hy => (hfull y hy).elim fun x hx => ⟨x,(hf.1.1.1.1 x y hx).1,hx⟩⟩,
      initial_order_iff A R B S F hf⟩
  · intro hn
    have hex : ∃ y, B y ∧ ¬ ∃ x, F x y := by
      refine (em (∃ y, B y ∧ ¬ ∃ x, F x y)).elim (fun h => h) ?_
      intro h
      exact (hn (fun y hy => (em (∃ x, F x y)).elim (fun h => h) (fun hny => (h ⟨y,hy,hny⟩).elim))).elim
    obtain ⟨b,hb,hnb,cb⟩ := downclosed_cut B (fun y => ∃ x, F x y) S hs (initial_range_downclosed A R B S F hf) hex
    have hbounds : ∀ x y, F x y → A x ∧ Segment B S b y := fun x y h =>
      ⟨(hf.1.1.1.1 x y h).1,(hf.1.1.1.1 x y h).2,(cb y (hf.1.1.1.1 x y h).2).mpr ⟨x,h⟩⟩
    have hm : Maps F A (Segment B S b) := ⟨hbounds,
      fun x hx => (hf.1.1.1.2.1 x hx).elim fun y hy => ⟨y,(hbounds x y hy.2).2,hy.2⟩,hf.1.1.1.2.2⟩
    refine Or.inr ⟨b,hb,⟨⟨hm,hf.1.1.2⟩,hm,?_⟩,?_⟩
    · intro y hy
      obtain ⟨x,hxy⟩ := (cb y hy.1).mp hy.2
      exact ⟨x,(hbounds x y hxy).1,hxy⟩
    · intro x y u v hx hy
      exact ⟨fun h => ⟨(hbounds x u hx).2,(hbounds y v hy).2,(initial_order_iff A R B S F hf x y u v hx hy).mp h⟩,
        fun h => (initial_order_iff A R B S F hf x y u v hx hy).mpr h.2.2⟩

theorem wellOrder_trichotomy (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (hw : WellOrderOn A R) (hs : WellOrderOn B S) :
    (∃ F, OrderIso F A R B S) ∨
    (∃ b, B b ∧ ∃ F, OrderIso F A R (Segment B S b) (RestrictOrder S (Segment B S b))) ∨
    (∃ a, A a ∧ ∃ G, OrderIso G B S (Segment A R a) (RestrictOrder R (Segment A R a))) := by
  obtain ⟨F,hf⟩ | ⟨G,hg⟩ := wellOrder_comparison A R B S hw hs
  · obtain hi | ⟨b,hb,hi⟩ := initial_embedding_classification A R B S F hs hf
    · exact Or.inl ⟨F,hi⟩
    · exact Or.inr (Or.inl ⟨b,hb,F,hi⟩)
  · obtain hi | ⟨a,ha,hi⟩ := initial_embedding_classification B S A R G hw hg
    · exact Or.inl ⟨fun x y => G y x,orderIso_inverse B A S R G hi⟩
    · exact Or.inr (Or.inr ⟨a,ha,G,hi⟩)
#classicism_check initial_order_iff initial_embedding_classification wellOrder_trichotomy
#classicism_types initial_order_iff initial_embedding_classification wellOrder_trichotomy
end Classicism.MathematicalContingency
