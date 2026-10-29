import Classicism.Results.MathematicalContingency.OrdinalExistence
/-! Conditional typed Hartogs diagonal. Representation remains an explicit obligation. -/
namespace Classicism.MathematicalContingency
variable {σ τ υ : Type} [Ty σ] [Ty τ] [Ty υ]
def RelImage (F : σ → τ → Prop) : τ → Prop := fun y => ∃ x, F x y
def ImageOrder (F : σ → τ → Prop) (L : σ → σ → Prop) : τ → τ → Prop :=
  fun u v => ∃ x y, F x u ∧ F y v ∧ L x y

theorem injects_into_image (F : σ → τ → Prop) (A : σ → Prop) (B : τ → Prop)
    (hf : Injects F A B) : Injects F A (RelImage F) :=
  ⟨⟨fun x y h => ⟨(hf.1.1 x y h).1,x,h⟩,
    fun x hx => (hf.1.2.1 x hx).elim fun y hy => ⟨y,⟨x,hy.2⟩,hy.2⟩,hf.1.2.2⟩,hf.2⟩
theorem image_subset (F : σ → τ → Prop) (A : σ → Prop) (B : τ → Prop)
    (hf : Maps F A B) : ∀ y, RelImage F y → B y :=
  fun y hy => hy.elim fun x hx => (hf.1 x y hx).2

theorem image_wellOrder (F : σ → τ → Prop) (A : σ → Prop) (B : τ → Prop)
    (L : σ → σ → Prop) (hf : Injects F A B) (hw : WellOrderOn A L) :
    WellOrderOn (RelImage F) (ImageOrder F L) := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro u v h; obtain ⟨x,y,hxu,hyv,_⟩ := h
    exact ⟨⟨x,hxu⟩,y,hyv⟩
  · intro u _ h
    obtain ⟨x,y,hxu,hyu,hxy⟩ := h
    have he := hf.2 x y u hxu hyu
    exact hw.1.2.1 x (hf.1.1 x u hxu).1 (Eq.mp (congrArg (fun z => L x z) he.symm) hxy)
  · intro u v w _ _ _ huv hvw
    obtain ⟨x,y,hxu,hyv,hxy⟩ := huv
    obtain ⟨z,q,hzv,hqw,hzq⟩ := hvw
    have he := hf.2 y z v hyv hzv
    have hyq : L y q := he.symm ▸ hzq
    exact ⟨x,q,hxu,hqw,hw.1.2.2.1 x y q (hf.1.1 x u hxu).1
      (hf.1.1 y v hyv).1 (hf.1.1 q w hqw).1 hxy hyq⟩
  · intro u v hu hv
    obtain ⟨x,hxu⟩ := hu
    obtain ⟨y,hyv⟩ := hv
    obtain he | hxy | hyx := hw.1.2.2.2 x y (hf.1.1 x u hxu).1 (hf.1.1 y v hyv).1
    · exact Or.inl (hf.1.2.2 x u v hxu (he.symm ▸ hyv))
    · exact Or.inr (Or.inl ⟨x,y,hxu,hyv,hxy⟩)
    · exact Or.inr (Or.inr ⟨y,x,hyv,hxu,hyx⟩)
  · intro X hX he
    let D : σ → Prop := fun x => ∃ u, F x u ∧ X u
    have hd : ∀ x, D x → A x := fun x hx => hx.elim fun u hu => (hf.1.1 x u hu.1).1
    have hdne : ∃ x, D x := he.elim fun u hu => (hX u hu).elim fun x hx => ⟨x,u,hx,hu⟩
    obtain ⟨x,hx,hmin⟩ := hw.2 D hd hdne
    obtain ⟨u,hxu,hu⟩ := hx
    refine ⟨u,hu,?_⟩
    intro v hv hvu
    obtain ⟨w,z,hwv,hzu,hwz⟩ := hvu
    have he := hf.2 z x u hzu hxu
    exact hmin w ⟨v,hwv,hv⟩ (Eq.mp (congrArg (fun q => L w q) he) hwz)

theorem image_orderEmbedding (F : σ → τ → Prop) (A : σ → Prop) (B : τ → Prop)
    (L : σ → σ → Prop) (hf : Injects F A B) :
    OrderEmbedsBy F A L (RelImage F) (ImageOrder F L) :=
  ⟨injects_into_image F A B hf,fun x y u v hx hy h => ⟨x,y,hx,hy,h⟩⟩

theorem orderEmbedding_compose (A : σ → Prop) (B : τ → Prop) (C : υ → Prop)
    (L : σ → σ → Prop) (M : τ → τ → Prop) (N : υ → υ → Prop)
    (F : σ → τ → Prop) (G : τ → υ → Prop)
    (hf : OrderEmbedsBy F A L B M) (hg : OrderEmbedsBy G B M C N) :
    OrderEmbedsBy (RelCompose F G) A L C N := by
  refine ⟨injects_compose F G A B C hf.1 hg.1,?_⟩
  intro x y u v hx hy hxy
  obtain ⟨a,hxa,hau⟩ := hx
  obtain ⟨b,hyb,hbv⟩ := hy
  exact hg.2 a b u v hau hbv (hf.2 x y a b hxa hyb hxy)

def SegmentUniversal (A : σ → Prop) (H : τ → Prop) (L : τ → τ → Prop) : Prop :=
  ∀ B M, (∀ x, B x → A x) → WellOrderOn B M →
    ∃ a, H a ∧ ∃ F, OrderEmbedsBy F B M (Segment H L a) (RestrictOrder L (Segment H L a))

theorem hartogs_diagonal (A : σ → Prop) (H : τ → Prop) (L : τ → τ → Prop)
    (hw : WellOrderOn H L) (hu : SegmentUniversal A H L) : ¬ Embeds H A := by
  intro h
  obtain ⟨F,hf⟩ := h
  obtain ⟨a,ha,G,hg⟩ := hu (RelImage F) (ImageOrder F L) (image_subset F H A hf.1)
    (image_wellOrder F H A L hf hw)
  exact no_embedding_into_proper_segment H L hw a ha (RelCompose F G)
    (orderEmbedding_compose H _ _ L _ _ F G (image_orderEmbedding F H A L hf) hg)

def HartogsRepresentation (A : σ → Prop) : Prop :=
  WellOrderOn (HartogsCarrier A) (HartogsOrder A) ∧
  SegmentUniversal A (HartogsCarrier A) (HartogsOrder A) ∧
  ∀ α, HartogsCarrier A α → Embeds (Segment (HartogsCarrier A) (HartogsOrder A) α) A

theorem inductive_hartogs_of_representation (A : σ → Prop) (h : HartogsRepresentation A) :
    WellOrderOn (HartogsCarrier A) (HartogsOrder A) ∧ ¬ Embeds (HartogsCarrier A) A ∧
      ∀ α, HartogsCarrier A α → Embeds (Segment (HartogsCarrier A) (HartogsOrder A) α) A :=
  ⟨h.1,hartogs_diagonal A _ _ h.1 h.2.1,h.2.2⟩

theorem hartogs_realizes_suborders (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A B : σ → Prop) (R : σ → σ → Prop) (hb : ∀ x, B x → A x) (hw : WellOrderOn B R) :
    ∃ α, HartogsCarrier A α ∧ ExactOrdinal α R B := by
  obtain ⟨α,hα,he⟩ := exact_ordinal_exists rc B R hw
  exact ⟨α,⟨hα,R,B,hb,hw,he⟩,he⟩

theorem hartogsOrder_irrefl (A : σ → Prop) (α : OrdinalCarrier σ) : ¬ HartogsOrder A α α := by
  intro h
  obtain ⟨R,B,_,hw,he,b,hb,hα⟩ := h.2.2
  exact he.2 ⟨hw,b,hb,hα.1⟩
theorem hartogsOrder_not_below_zero (A : σ → Prop) (α : OrdinalCarrier σ) :
    ¬ HartogsOrder A α (OrdZero σ) := by
  intro h
  obtain ⟨R,B,_,_,he,b,hb,_⟩ := h.2.2
  exact ((exactOrdZero_iff_empty R B).mp he).2 b hb

theorem hartogsOrder_zero_least (A : σ → Prop) (α : OrdinalCarrier σ)
    (hα : HartogsCarrier A α) (hn : α ≠ OrdZero σ) : HartogsOrder A (OrdZero σ) α := by
  obtain ⟨R,B,hb,hw,he⟩ := hα.2
  have hne : ∃ b, B b := (em (∃ b, B b)).elim (fun h => h) (fun h =>
    (hn (ordinal_empty_unique α hα.1 R B (fun b hb => h ⟨b,hb⟩) he.1)).elim)
  obtain ⟨b,hb',hm⟩ := hw.2 B (fun _ h => h) hne
  refine ⟨hartogsCarrier_zero A,hα,R,B,hb,hw,he,b,hb',?_⟩
  exact (exactOrdZero_iff_empty _ _).mpr
    ⟨wellOrder_restrict B _ R hw (fun _ h => h.1),fun x hx => hm x hx.1 hx.2⟩

#classicism_check injects_into_image image_subset image_wellOrder image_orderEmbedding orderEmbedding_compose
  hartogs_diagonal inductive_hartogs_of_representation hartogs_realizes_suborders hartogsOrder_irrefl
  hartogsOrder_not_below_zero hartogsOrder_zero_least
#classicism_types injects_into_image image_subset image_wellOrder image_orderEmbedding orderEmbedding_compose
  hartogs_diagonal inductive_hartogs_of_representation hartogs_realizes_suborders hartogsOrder_irrefl
  hartogsOrder_not_below_zero hartogsOrder_zero_least
end Classicism.MathematicalContingency
