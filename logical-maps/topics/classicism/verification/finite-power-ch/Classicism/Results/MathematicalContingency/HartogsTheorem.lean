import Classicism.Results.MathematicalContingency.HartogsRanks
namespace Classicism.MathematicalContingency
variable {σ τ : Type} [Ty σ] [Ty τ]
theorem wellOrder_of_orderIso (A : σ → Prop) (R : σ → σ → Prop)
    (B : τ → Prop) (S : τ → τ → Prop) (F : σ → τ → Prop)
    (hw : WellOrderOn A R) (hf : OrderIso F A R B S)
    (hs : StrictOrderOn B S) : WellOrderOn B S := by
  refine ⟨hs,?_⟩
  intro X hX hne
  let D : σ → Prop := fun x => ∃ y, F x y ∧ X y
  have hd : ∀ x, D x → A x := fun x hx => hx.elim fun y hy => (hf.1.1.1.1 x y hy.1).1
  have hdn : ∃ x, D x := hne.elim fun y hy => (hf.1.2.2 y (hX y hy)).elim fun x hx => ⟨x,y,hx.2,hy⟩
  obtain ⟨x,hx,hm⟩ := hw.2 D hd hdn
  obtain ⟨y,hxy,hy⟩ := hx
  refine ⟨y,hy,?_⟩
  intro z hz hzy
  obtain ⟨w,hwA,hwz⟩ := hf.1.2.2 z (hX z hz)
  exact hm w ⟨z,hwz,hz⟩ ((hf.2 w x z y hwz hxy).mpr hzy)

theorem strictOrder_restrict (A B : σ → Prop) (R : σ → σ → Prop)
    (hw : StrictOrderOn A R) (hb : ∀ x, B x → A x) : StrictOrderOn B (RestrictOrder R B) := by
  refine ⟨fun _ _ h => ⟨h.1,h.2.1⟩,fun x hx h => hw.2.1 x (hb x hx) h.2.2,?_,?_⟩
  · intro x y z hx hy hz hxy hyz
    exact ⟨hx,hz,hw.2.2.1 x y z (hb x hx) (hb y hy) (hb z hz) hxy.2.2 hyz.2.2⟩
  · intro x y hx hy
    exact (hw.2.2.2 x y (hb x hx) (hb y hy)).elim Or.inl
      (fun h => Or.inr (h.elim (fun hxy => Or.inl ⟨hx,hy,hxy⟩) (fun hyx => Or.inr ⟨hy,hx,hyx⟩)))

theorem hartogs_segment_strictOrder (A : σ → Prop) (α : OrdinalCarrier σ) :
    StrictOrderOn (Segment (HartogsCarrier A) (HartogsOrder A) α)
      (RestrictOrder (HartogsOrder A) (Segment (HartogsCarrier A) (HartogsOrder A) α)) := by
  have hw := hartogs_strictOrder A
  refine ⟨fun _ _ h => ⟨h.1,h.2.1⟩,fun x hx h => hw.2.1 x hx.1 h.2.2,?_,?_⟩
  · intro x y z hx hy hz hxy hyz
    exact ⟨hx,hz,hw.2.2.1 x y z hx.1 hy.1 hz.1 hxy.2.2 hyz.2.2⟩
  · intro x y hx hy
    exact (hw.2.2.2 x y hx.1 hy.1).elim Or.inl
      (fun h => Or.inr (h.elim (fun hxy => Or.inl ⟨hx,hy,hxy⟩) (fun hyx => Or.inr ⟨hy,hx,hyx⟩)))

def RankPreimage (B : σ → Prop) (R : σ → σ → Prop) (X : OrdinalCarrier σ → Prop) : σ → Prop :=
  fun x => ∃ β, RankGraph B R x β ∧ X β

theorem rank_preimage_subset (B : σ → Prop) (R : σ → σ → Prop) (X : OrdinalCarrier σ → Prop) :
    ∀ x, RankPreimage B R X x → B x :=
  fun x hx => hx.elim fun β hβ => hβ.1.1

theorem rank_preimage_nonempty (A B : σ → Prop) (R : σ → σ → Prop)
    (α : OrdinalCarrier σ) (he : ExactOrdinal α R B) (X : OrdinalCarrier σ → Prop)
    (hX : ∀ β, X β → Segment (HartogsCarrier A) (HartogsOrder A) α β)
    (hne : ∃ β, X β) : ∃ x, RankPreimage B R X x :=
  hne.elim fun β hβ => (rank_onto A B R α he β (hX β hβ)).elim fun x hx => ⟨x,β,hx.2,hβ⟩

theorem rank_preimage_minimum (A B : σ → Prop) (R : σ → σ → Prop)
    (hb : ∀ x, B x → A x) (hw : WellOrderOn B R)
    (α : OrdinalCarrier σ) (he : ExactOrdinal α R B) (X : OrdinalCarrier σ → Prop)
    (hX : ∀ β, X β → Segment (HartogsCarrier A) (HartogsOrder A) α β)
    (x : σ) (hx : RankPreimage B R X x)
    (hm : ∀ w, RankPreimage B R X w → ¬ R w x) :
    ∃ β, X β ∧ ∀ γ, X γ → ¬ HartogsOrder A γ β := by
  obtain ⟨β,hxβ,hβ⟩ := hx
  refine ⟨β,hβ,?_⟩
  intro γ hγ hγβ
  obtain ⟨w,hwB,hwγ⟩ := rank_onto A B R α he γ (hX γ hγ)
  exact hm w ⟨γ,hwγ,hγ⟩ ((rank_order_iff A B R hb hw w x γ β hwγ hxβ).mpr hγβ)

theorem rank_subset_minimum (A B : σ → Prop) (R : σ → σ → Prop)
    (hb : ∀ x, B x → A x) (hw : WellOrderOn B R)
    (α : OrdinalCarrier σ) (he : ExactOrdinal α R B) (X : OrdinalCarrier σ → Prop)
    (hX : ∀ β, X β → Segment (HartogsCarrier A) (HartogsOrder A) α β)
    (hne : ∃ β, X β) : ∃ β, X β ∧ ∀ γ, X γ → ¬ HartogsOrder A γ β := by
  obtain ⟨x,hx,hm⟩ := hw.2 (RankPreimage B R X) (rank_preimage_subset B R X)
    (rank_preimage_nonempty A B R α he X hX hne)
  exact rank_preimage_minimum A B R hb hw α he X hX x hx hm

theorem hartogs_segment_wellOrder (_rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) (α : OrdinalCarrier σ) (hα : HartogsCarrier A α) :
    WellOrderOn (Segment (HartogsCarrier A) (HartogsOrder A) α)
      (RestrictOrder (HartogsOrder A) (Segment (HartogsCarrier A) (HartogsOrder A) α)) := by
  obtain ⟨R,B,hb,hw,he⟩ := hα.2
  refine ⟨hartogs_segment_strictOrder A α,?_⟩
  intro X hX hne
  obtain ⟨β,hβ,hm⟩ := rank_subset_minimum A B R hb hw α he X hX hne
  exact ⟨β,hβ,fun γ hγ hγβ => hm γ hγ hγβ.2.2⟩

theorem hartogs_wellOrder (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) : WellOrderOn (HartogsCarrier A) (HartogsOrder A) := by
  refine ⟨hartogs_strictOrder A,?_⟩
  intro X hX hne
  obtain ⟨α,hα⟩ := hne
  refine (em (∃ β, X β ∧ HartogsOrder A β α)).elim ?_ ?_
  · intro hbelow
    have hw := hartogs_segment_wellOrder rc A α (hX α hα)
    obtain ⟨β,hβ,hm⟩ := hw.2 (fun β => X β ∧ HartogsOrder A β α)
      (fun β h => ⟨hX β h.1,h.2⟩) hbelow
    refine ⟨β,hβ.1,?_⟩
    intro γ hγ hγβ
    have hγα := hartogs_lt_trans A γ β α hγβ hβ.2
    exact hm γ ⟨hγ,hγα⟩ ⟨⟨hX γ hγ,hγα⟩,⟨hX β hβ.1,hβ.2⟩,hγβ⟩
  · intro hn
    exact ⟨α,hα,fun β hβ hβα => hn ⟨β,hβ,hβα⟩⟩

theorem hartogs_segment_universal (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) : SegmentUniversal A (HartogsCarrier A) (HartogsOrder A) := by
  intro B R hb hw
  obtain ⟨α,hα,he⟩ := exact_ordinal_exists rc B R hw
  refine ⟨α,⟨hα,R,B,hb,hw,he⟩,RankGraph B R,?_,?_⟩
  · exact ⟨rank_maps rc A B R hb hw α hα he,rank_injective B R hw⟩
  · intro x y β γ hx hy hxy
    exact ⟨rank_below A B R hb hw α hα he x β hx,
      rank_below A B R hb hw α hα he y γ hy,
      rank_increasing A B R hb hw x y β γ hx hy hxy⟩

theorem hartogs_segment_embeds (A : σ → Prop) (α : OrdinalCarrier σ)
    (hα : HartogsCarrier A α) :
    Embeds (Segment (HartogsCarrier A) (HartogsOrder A) α) A := by
  obtain ⟨R,B,hb,hw,he⟩ := hα.2
  refine ⟨fun β x => RankGraph B R x β,⟨?_,?_,?_⟩,?_⟩
  · intro β x hx
    exact ⟨rank_below A B R hb hw α hα.1 he x β hx,hb x hx.1⟩
  · intro β hβ
    obtain ⟨x,hx,hxβ⟩ := rank_onto A B R α he β hβ
    exact ⟨x,hb x hx,hxβ⟩
  · intro β x z hx hz
    exact rank_injective B R hw x z β hx hz
  · intro β γ x hx hy
    exact rank_functional B R x β γ hx hy

theorem hartogs_representation (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) : HartogsRepresentation A :=
  ⟨hartogs_wellOrder rc A,hartogs_segment_universal rc A,hartogs_segment_embeds A⟩

theorem inductive_hartogs (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) :
    WellOrderOn (HartogsCarrier A) (HartogsOrder A) ∧ ¬ Embeds (HartogsCarrier A) A ∧
      ∀ α, HartogsCarrier A α → Embeds (Segment (HartogsCarrier A) (HartogsOrder A) α) A :=
  inductive_hartogs_of_representation A (hartogs_representation rc A)

theorem hartogs_initialCardinal (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) : InitialCardinal (HartogsCarrier A) (HartogsOrder A) := by
  have h := inductive_hartogs rc A
  exact ⟨h.1,fun α hα hi => h.2.1 (embeds_trans _ _ A hi (h.2.2 α hα))⟩

theorem necessary_inductive_hartogs (rc : P.NecRigidComprehension (OrdinalCarrier σ → Prop))
    (A : σ → Prop) :
    □ (WellOrderOn (HartogsCarrier A) (HartogsOrder A) ∧ ¬ Embeds (HartogsCarrier A) A ∧
      ∀ α, HartogsCarrier A α → Embeds (Segment (HartogsCarrier A) (HartogsOrder A) α) A) :=
  modal_K _ _ (nec% (fun (h : P.RigidComprehension (OrdinalCarrier σ → Prop)) => inductive_hartogs h A)) rc
#classicism_check wellOrder_of_orderIso strictOrder_restrict hartogs_segment_strictOrder rank_preimage_subset
  rank_preimage_nonempty rank_preimage_minimum rank_subset_minimum hartogs_segment_wellOrder hartogs_wellOrder
  hartogs_segment_universal hartogs_segment_embeds hartogs_representation inductive_hartogs hartogs_initialCardinal necessary_inductive_hartogs
#classicism_types wellOrder_of_orderIso strictOrder_restrict hartogs_segment_strictOrder rank_preimage_subset
  rank_preimage_nonempty rank_preimage_minimum rank_subset_minimum hartogs_segment_wellOrder hartogs_wellOrder
  hartogs_segment_universal hartogs_segment_embeds hartogs_representation inductive_hartogs hartogs_initialCardinal necessary_inductive_hartogs
end Classicism.MathematicalContingency
