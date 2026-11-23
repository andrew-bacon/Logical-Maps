import Classicism.Results.MathematicalContingency.InductiveOrdinals
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
def InitialEmbedding (F : σ → τ → Prop) (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) : Prop :=
  OrderEmbedsBy F A R B S ∧ ∀ x y z, F x y → B z → S z y → ∃ w, R w x ∧ F w z

def UpwardOrdinal (α : OrdinalCarrier σ) : Prop :=
  ∀ A B R S F, WellOrderOn A R → WellOrderOn B S → InitialEmbedding F A R B S → α R A → α S B

theorem initialEmbedding_segments (A : σ → Prop) (B : τ → Prop)
    (R : σ → σ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hw : WellOrderOn A R) (hs : WellOrderOn B S) (hf : InitialEmbedding F A R B S)
    (a : σ) (b : τ) (hab : F a b) :
    InitialEmbedding (fun x y => Segment A R a x ∧ Segment B S b y ∧ F x y)
      (Segment A R a) (RestrictOrder R (Segment A R a))
      (Segment B S b) (RestrictOrder S (Segment B S b)) := by
  refine ⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x y h; exact ⟨h.1,h.2.1⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hf.1.1.1.2.1 x hx.1
    have hseg : Segment B S b y := ⟨hy,hf.1.2 x a y b hxy hab hx.2⟩
    exact ⟨y,hseg,hx,hseg,hxy⟩
  · intro x y z hy hz; exact hf.1.1.1.2.2 x y z hy.2.2 hz.2.2
  · intro x z y hx hz; exact hf.1.1.2 x z y hx.2.2 hz.2.2
  · intro x y u v hxu hyv hxy; exact ⟨hxu.2.1,hyv.2.1,hf.1.2 x y u v hxu.2.2 hyv.2.2 hxy.2.2⟩
  · intro x y z hxy hz hzy
    obtain ⟨w,hwx,hwz⟩ := hf.2 x y z hxy.2.2 hz.1 hzy.2.2
    have hwA := (hf.1.1.1.1 w z hwz).1
    have hwa : Segment A R a w := ⟨hwA,hw.1.2.2.1 w x a hwA hxy.1.1
      (hf.1.1.1.1 a b hab).1 hwx hxy.1.2⟩
    exact ⟨w,⟨hwa,hxy.1,hwx⟩,hwa,hz,hwz⟩

theorem upward_zero : UpwardOrdinal (OrdZero σ) := fun _ _ _ _ _ _ hs _ _ => hs
theorem upward_suc (α : OrdinalCarrier σ) (h : UpwardOrdinal α) : UpwardOrdinal (OrdSuc α) := by
  intro A B R S F hw hs hf ha
  obtain ⟨a,ha,hα⟩ := ha.2
  obtain ⟨b,hb,hab⟩ := hf.1.1.1.2.1 a ha
  exact ⟨hs,b,hb,h _ _ _ _ _ (wellOrder_restrict A _ R hw (fun _ hx => hx.1))
    (wellOrder_restrict B _ S hs (fun _ hx => hx.1))
    (initialEmbedding_segments A B R S F hw hs hf a b hab) hα⟩
theorem upward_lim (Y : OrdinalCarrier σ → Prop) (h : ∀ β, Y β → UpwardOrdinal β) :
    UpwardOrdinal (OrdLim Y) := fun A B R S F hw hs hf ha =>
  ⟨hs,fun β hβ => h β hβ A B R S F hw hs hf (ha.2 β hβ)⟩

theorem ordinal_upward_necessary (α : OrdinalCarrier σ) (hα : Ordinal α) : □ (UpwardOrdinal α) := by
  apply ordinal_induction (fun α => □ (UpwardOrdinal α)) (nec% (@upward_zero σ _)) ?_ ?_ α hα
  · intro β _ ih
    exact modal_K _ _ (nec% (upward_suc β)) ih
  · intro Y hy ih
    have hb := restricted_barcan_unary Y UpwardOrdinal hy (fun β hβ => (ih β hβ).2)
    exact modal_K _ _ (nec% (upward_lim Y)) hb

theorem ordinal_upward (α : OrdinalCarrier σ) (hα : Ordinal α) : UpwardOrdinal α :=
  box_elim (ordinal_upward_necessary α hα)

theorem orderIso_initial (A : σ → Prop) (B : τ → Prop) (R : σ → σ → Prop)
    (S : τ → τ → Prop) (F : σ → τ → Prop) (h : OrderIso F A R B S) : InitialEmbedding F A R B S := by
  refine ⟨⟨h.1.1,fun x y u v hx hy hr => (h.2 x y u v hx hy).mp hr⟩,?_⟩
  intro x y z hxy hz hzy
  obtain ⟨w,hw,hwz⟩ := h.1.2.2 z hz
  exact ⟨w,(h.2 w x z y hwz hxy).mpr hzy,hwz⟩

theorem orderIso_inverse (A : σ → Prop) (B : τ → Prop) (R : σ → σ → Prop)
    (S : τ → τ → Prop) (F : σ → τ → Prop) (h : OrderIso F A R B S) :
    OrderIso (fun y x => F x y) B S A R := by
  have hm : Maps (fun y x => F x y) B A :=
    ⟨fun y x hx => ⟨(h.1.1.1.1 x y hx).2,(h.1.1.1.1 x y hx).1⟩,
      h.1.2.2,fun y x z hx hz => h.1.1.2 x z y hx hz⟩
  exact ⟨⟨⟨hm,fun y z x hy hz => h.1.1.1.2.2 x y z hy hz⟩,hm,h.1.1.1.2.1⟩,
    fun u v x y hxu hyv => (h.2 x y u v hxu hyv).symm⟩

theorem ordinal_iso_forward (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A B : σ → Prop) (R S : σ → σ → Prop) (F : σ → σ → Prop)
    (hw : WellOrderOn A R) (hs : WellOrderOn B S) (hf : OrderIso F A R B S) (h : α R A) : α S B :=
  ordinal_upward α hα A B R S F hw hs (orderIso_initial A B R S F hf) h

theorem upward_iso_iff (α : OrdinalCarrier σ) (hα : UpwardOrdinal α)
    (A B : σ → Prop) (R S : σ → σ → Prop) (F : σ → σ → Prop)
    (hw : WellOrderOn A R) (hs : WellOrderOn B S) (hf : OrderIso F A R B S) : α R A ↔ α S B :=
  ⟨hα A B R S F hw hs (orderIso_initial A B R S F hf),
    hα B A S R (fun y x => F x y) hs hw (orderIso_initial B A S R _ (orderIso_inverse A B R S F hf))⟩

theorem ordinal_iso_necessary (α : OrdinalCarrier σ) (hα : Ordinal α) :
    □ (∀ A B R S F, WellOrderOn A R → WellOrderOn B S → OrderIso F A R B S → (α R A ↔ α S B)) :=
  modal_K _ _ (nec% (upward_iso_iff α)) (ordinal_upward_necessary α hα)

theorem segment_inclusion_initial (A : σ → Prop) (R : σ → σ → Prop) (hw : WellOrderOn A R)
    (a : σ) (ha : A a) : InitialEmbedding (fun x y => Segment A R a x ∧ x = y)
      (Segment A R a) (RestrictOrder R (Segment A R a)) A R := by
  refine ⟨⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro x y h; exact ⟨h.1,h.2 ▸ h.1.1⟩
  · intro x hx; exact ⟨x,hx.1,hx,rfl⟩
  · intro x y z hy hz; exact hy.2.symm.trans hz.2
  · intro x z y hx hz; exact hx.2.trans hz.2.symm
  · intro x y u v hx hy h; exact hx.2 ▸ hy.2 ▸ h.2.2
  · intro x y z h hz hzy
    have hzx : R z x := h.2.symm ▸ hzy
    have hza : Segment A R a z := ⟨hz,hw.1.2.2.1 z x a hz h.1.1 ha hzx h.1.2⟩
    exact ⟨z,⟨hza,h.1,hzx⟩,hza,rfl⟩

theorem upward_suc_downward (α : OrdinalCarrier σ) (h : UpwardOrdinal α) :
    ∀ R A, OrdSuc α R A → α R A := by
  intro R A hs
  obtain ⟨a,ha,hα⟩ := hs.2
  exact h _ _ _ _ _ (wellOrder_restrict A _ R hs.1 (fun _ hx => hx.1)) hs.1
    (segment_inclusion_initial A R hs.1 a ha) hα

theorem ordinal_suc_downward_necessary (α : OrdinalCarrier σ) (hα : Ordinal α) :
    □ (∀ R A, OrdSuc α R A → α R A) :=
  modal_K _ _ (nec% (upward_suc_downward α)) (ordinal_upward_necessary α hα)

#classicism_check initialEmbedding_segments upward_zero upward_suc upward_lim ordinal_upward_necessary
  ordinal_upward orderIso_initial orderIso_inverse ordinal_iso_forward upward_iso_iff ordinal_iso_necessary
  segment_inclusion_initial upward_suc_downward ordinal_suc_downward_necessary
#classicism_types initialEmbedding_segments upward_zero upward_suc upward_lim ordinal_upward_necessary
  ordinal_upward orderIso_initial orderIso_inverse ordinal_iso_forward upward_iso_iff ordinal_iso_necessary
  segment_inclusion_initial upward_suc_downward ordinal_suc_downward_necessary
end Classicism.MathematicalContingency
