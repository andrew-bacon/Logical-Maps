import Classicism.Results.MathematicalContingency.ModalLemmas
/-! Relational maps and well-orders. OpenAI Codex, prompted by Andrew Bacon. -/
namespace Classicism.MathematicalContingency
variable {σ τ υ : Type} [Ty σ] [Ty τ] [Ty υ]
def RelCompose (F : σ → τ → Prop) (G : τ → υ → Prop) : σ → υ → Prop :=
  fun x z => ∃ y, F x y ∧ G y z

theorem maps_compose (F : σ → τ → Prop) (G : τ → υ → Prop)
    (A : σ → Prop) (B : τ → Prop) (C : υ → Prop)
    (hf : Maps F A B) (hg : Maps G B C) : Maps (RelCompose F G) A C := by
  refine ⟨?_,?_,?_⟩
  · intro x z h; obtain ⟨y,hxy,hyz⟩ := h
    exact ⟨(hf.1 x y hxy).1,(hg.1 y z hyz).2⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hf.2.1 x hx
    obtain ⟨z,hz,hyz⟩ := hg.2.1 y hy
    exact ⟨z,hz,y,hxy,hyz⟩
  · intro x z w hz hw
    obtain ⟨y,hxy,hyz⟩ := hz
    obtain ⟨v,hxv,hvw⟩ := hw
    have he := hf.2.2 x y v hxy hxv
    subst v
    exact hg.2.2 y z w hyz hvw

theorem injects_compose (F : σ → τ → Prop) (G : τ → υ → Prop)
    (A : σ → Prop) (B : τ → Prop) (C : υ → Prop)
    (hf : Injects F A B) (hg : Injects G B C) : Injects (RelCompose F G) A C := by
  refine ⟨maps_compose F G A B C hf.1 hg.1,?_⟩
  intro x w z hx hw
  obtain ⟨y,hxy,hyz⟩ := hx
  obtain ⟨v,hwv,hvz⟩ := hw
  have he := hg.2 y v z hyz hvz
  subst v
  exact hf.2 x w y hxy hwv

theorem embeds_trans (A : σ → Prop) (B : τ → Prop) (C : υ → Prop)
    (h : Embeds A B) (k : Embeds B C) : Embeds A C :=
  h.elim fun F hf => k.elim fun G hg => ⟨RelCompose F G, injects_compose F G A B C hf hg⟩
theorem embeds_of_subset (A B : σ → Prop) (h : ∀ x, A x → B x) : Embeds A B := by
  refine ⟨fun x y => A x ∧ x = y, ⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro x y hx; exact ⟨hx.1,hx.2 ▸ h x hx.1⟩
  · intro x hx; exact ⟨x,h x hx,hx,rfl⟩
  · intro x y z hy hz; exact hy.2.symm.trans hz.2
  · intro x z y hx hz; exact hx.2.trans hz.2.symm
theorem embeds_refl (A : σ → Prop) : Embeds A A := embeds_of_subset A A (fun _ h => h)
theorem smaller_irrefl (A : σ → Prop) : ¬ Smaller A A := fun h => h.2 h.1
theorem smaller_trans (A : σ → Prop) (B : τ → Prop) (C : υ → Prop)
    (h : Smaller A B) (k : Smaller B C) : Smaller A C :=
  ⟨embeds_trans A B C h.1 k.1,fun rev => h.2 (embeds_trans B C A k.1 rev)⟩
theorem small_implies_smaller (K : σ → Prop) (L : σ → σ → Prop)
    (B : τ → Prop) (hk : InitialCardinal K L) (hb : Small K L B) : Smaller B K := by
  obtain ⟨a,ha,hba⟩ := hb
  exact ⟨embeds_trans B _ K hba (embeds_of_subset _ _ (fun _ h => h.1)),
    fun hkb => hk.2 a ha (embeds_trans K B _ hkb hba)⟩

def RestrictOrder (L : σ → σ → Prop) (A : σ → Prop) : σ → σ → Prop :=
  fun x y => A x ∧ A y ∧ L x y

theorem wellOrder_restrict (A B : σ → Prop) (L : σ → σ → Prop)
    (hw : WellOrderOn A L) (hb : ∀ x, B x → A x) : WellOrderOn B (RestrictOrder L B) := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro x y h; exact ⟨h.1,h.2.1⟩
  · intro x hx h; exact hw.1.2.1 x (hb x hx) h.2.2
  · intro x y z hx hy hz hxy hyz
    exact ⟨hx,hz,hw.1.2.2.1 x y z (hb x hx) (hb y hy) (hb z hz) hxy.2.2 hyz.2.2⟩
  · intro x y hx hy
    exact (hw.1.2.2.2 x y (hb x hx) (hb y hy)).elim Or.inl
      (fun h => Or.inr (h.elim (fun hxy => Or.inl ⟨hx,hy,hxy⟩) (fun hyx => Or.inr ⟨hy,hx,hyx⟩)))
  · intro X hX he
    obtain ⟨x,hx,hm⟩ := hw.2 X (fun y hy => hb y (hX y hy)) he
    exact ⟨x,hx,fun y hy h => hm y hy h.2.2⟩

theorem wellOrder_induction (A : σ → Prop) (L : σ → σ → Prop) (hw : WellOrderOn A L)
    (P : σ → Prop) (step : ∀ x, A x → (∀ y, A y → L y x → P y) → P x) :
    ∀ x, A x → P x := by
  intro x hx
  refine (em (P x)).elim (fun h => h) ?_
  intro hn
  obtain ⟨a,ha,hm⟩ := hw.2 (fun y => A y ∧ ¬ P y) (fun _ h => h.1) ⟨x,hx,hn⟩
  exact (ha.2 (step a ha.1 (fun y hy hya => (em (P y)).elim (fun h => h)
    (fun h => (hm y ⟨hy,h⟩ hya).elim)))).elim

def OrderEmbedsBy (F : σ → τ → Prop) (A : σ → Prop) (L : σ → σ → Prop)
    (B : τ → Prop) (M : τ → τ → Prop) : Prop :=
  Injects F A B ∧ ∀ x y u v, F x u → F y v → L x y → M u v

theorem wellOrder_no_descent (A : σ → Prop) (L F : σ → σ → Prop)
    (hw : WellOrderOn A L) (hf : Maps F A A)
    (inc : ∀ x y u v, F x u → F y v → L x y → L u v) :
    ∀ x y, F x y → ¬ L y x := by
  have h := wellOrder_induction A L hw (fun x => ∀ y, F x y → ¬ L y x) (by
    intro x hx ih y hxy hyx
    have hy := (hf.1 x y hxy).2
    obtain ⟨z,hz,hyz⟩ := hf.2.1 y hy
    exact ih y hy hyx z hyz (inc y x z y hyz hxy hyx))
  exact fun x y hxy => h x (hf.1 x y hxy).1 y hxy

theorem no_embedding_into_proper_segment (A : σ → Prop) (L : σ → σ → Prop)
    (hw : WellOrderOn A L) (a : σ) (ha : A a) (F : σ → σ → Prop)
    (hf : OrderEmbedsBy F A L (Segment A L a) (RestrictOrder L (Segment A L a))) : False := by
  have hm : Maps F A A := ⟨fun x y h => ⟨(hf.1.1.1 x y h).1,(hf.1.1.1 x y h).2.1⟩,
    fun x hx => (hf.1.1.2.1 x hx).elim fun y hy => ⟨y,hy.1.1,hy.2⟩,hf.1.1.2.2⟩
  obtain ⟨y,hy,hay⟩ := hf.1.1.2.1 a ha
  exact wellOrder_no_descent A L F hw hm (fun x z u v hxu hzv hxz =>
    (hf.2 x z u v hxu hzv hxz).2.2) a y hay hy.2

#classicism_check maps_compose injects_compose embeds_trans embeds_of_subset embeds_refl smaller_irrefl
  smaller_trans small_implies_smaller wellOrder_restrict wellOrder_induction wellOrder_no_descent no_embedding_into_proper_segment
#classicism_types maps_compose injects_compose embeds_trans embeds_of_subset embeds_refl smaller_irrefl
  smaller_trans small_implies_smaller wellOrder_restrict wellOrder_induction wellOrder_no_descent no_embedding_into_proper_segment
end Classicism.MathematicalContingency
