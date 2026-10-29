import Classicism.Results.MathematicalContingency.Hartogs
import Classicism.Results.MathematicalContingency.OrdinalUniqueness
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]
theorem exactOrdinal_iso (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A B : σ → Prop) (R S : σ → σ → Prop) (F : σ → σ → Prop)
    (hw : WellOrderOn A R) (hs : WellOrderOn B S) (hf : OrderIso F A R B S) :
    ExactOrdinal α R A ↔ ExactOrdinal α S B := by
  have h := upward_iso_iff α (ordinal_upward α hα) A B R S F hw hs hf
  have k := upward_iso_iff (OrdSuc α) (ordinal_upward _ (ordinal_suc α hα)) A B R S F hw hs hf
  exact ⟨fun he => ⟨h.mp he.1,fun hn => he.2 (k.mpr hn)⟩,
    fun he => ⟨h.mpr he.1,fun hn => he.2 (k.mp hn)⟩⟩

theorem ordinal_exact_segment (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A : σ → Prop) (R : σ → σ → Prop) (hs : OrdSuc α R A) :
    ∃ a, A a ∧ ExactOrdinal α (RestrictOrder R (Segment A R a)) (Segment A R a) := by
  obtain ⟨a,ha,hm⟩ := hs.1.2 (fun a => A a ∧ α (RestrictOrder R (Segment A R a)) (Segment A R a))
    (fun _ h => h.1) hs.2
  refine ⟨a,ha.1,ha.2,?_⟩
  intro hn
  obtain ⟨b,hb,hαb⟩ := hn.2
  exact hm b ⟨hb.1,ordinal_segment_flatten α hα A R hs.1 a b ha.1 hb hαb⟩ hb.2

theorem hartogs_lt_implies (A : σ → Prop) (α β : OrdinalCarrier σ)
    (h : HartogsOrder A α β) : □ (OrdImplies β (OrdSuc α)) := by
  obtain ⟨R,B,hb,hw,he,b,hb',ha⟩ := h.2.2
  exact wellOrder_separation (Segment B R b) (RestrictOrder R (Segment B R b))
    (wellOrder_restrict B _ R hw (fun _ h => h.1)) α β h.1.1 h.2.1.1 ha.1
    (fun hβ => he.2 ⟨hw,b,hb',hβ⟩)

theorem hartogs_lt_of_suc (A : σ → Prop) (α β : OrdinalCarrier σ)
    (hα : HartogsCarrier A α) (hβ : HartogsCarrier A β)
    (R : σ → σ → Prop) (B : σ → Prop) (hb : ∀ x, B x → A x)
    (hw : WellOrderOn B R) (he : ExactOrdinal β R B) (hs : OrdSuc α R B) :
    HartogsOrder A α β := by
  obtain ⟨b,hb',ha⟩ := ordinal_exact_segment α hα.1 B R hs
  exact ⟨hα,hβ,R,B,hb,hw,he,b,hb',ha⟩

theorem hartogs_lt_of_implies (A : σ → Prop) (α β : OrdinalCarrier σ)
    (hα : HartogsCarrier A α) (hβ : HartogsCarrier A β)
    (h : □ (OrdImplies β (OrdSuc α))) : HartogsOrder A α β := by
  obtain ⟨R,B,hb,hw,he⟩ := hβ.2
  exact hartogs_lt_of_suc A α β hα hβ R B hb hw he (box_elim h R B he.1)

theorem hartogs_lt_trans (A : σ → Prop) (α β γ : OrdinalCarrier σ)
    (hab : HartogsOrder A α β) (hbc : HartogsOrder A β γ) : HartogsOrder A α γ := by
  obtain ⟨R,B,hb,hw,he⟩ := hbc.2.1.2
  have hβ : β R B := box_elim (ordinal_suc_downward_necessary β hab.2.1.1) R B
    (box_elim (hartogs_lt_implies A β γ hbc) R B he.1)
  exact hartogs_lt_of_suc A α γ hab.1 hbc.2.1 R B hb hw he
    (box_elim (hartogs_lt_implies A α β hab) R B hβ)

theorem hartogs_trichotomy (A : σ → Prop) (α β : OrdinalCarrier σ)
    (hα : HartogsCarrier A α) (hβ : HartogsCarrier A β) :
    α = β ∨ HartogsOrder A α β ∨ HartogsOrder A β α := by
  obtain ⟨R,B,hb,hw,he⟩ := hβ.2
  refine (em (α R B)).elim ?_ ?_
  · intro ha
    refine (em (OrdSuc α R B)).elim ?_ ?_
    · intro hs; exact Or.inr (Or.inl (hartogs_lt_of_suc A α β hα hβ R B hb hw he hs))
    · intro hn; exact Or.inl (exact_ordinal_unique α β hα.1 hβ.1 B R ⟨ha,hn⟩ he)
  · intro hn
    exact Or.inr (Or.inr (hartogs_lt_of_implies A β α hβ hα
      (wellOrder_separation B R hw β α hβ.1 hα.1 he.1 hn)))

theorem hartogs_strictOrder (A : σ → Prop) : StrictOrderOn (HartogsCarrier A) (HartogsOrder A) :=
  ⟨fun _ _ h => ⟨h.1,h.2.1⟩,fun α _ => hartogsOrder_irrefl A α,
    fun α β γ _ _ _ => hartogs_lt_trans A α β γ,hartogs_trichotomy A⟩

def RankGraph (B : σ → Prop) (R : σ → σ → Prop) (x : σ) (α : OrdinalCarrier σ) : Prop :=
  B x ∧ Ordinal α ∧ ExactOrdinal α (RestrictOrder R (Segment B R x)) (Segment B R x)

theorem rank_hartogs (A B : σ → Prop) (R : σ → σ → Prop) (hb : ∀ x, B x → A x)
    (hw : WellOrderOn B R) (x : σ) (α : OrdinalCarrier σ) (hx : RankGraph B R x α) :
    HartogsCarrier A α :=
  ⟨hx.2.1,RestrictOrder R (Segment B R x),Segment B R x,fun y hy => hb y hy.1,
    wellOrder_restrict B _ R hw (fun _ h => h.1),hx.2.2⟩

theorem rank_increasing (A B : σ → Prop) (R : σ → σ → Prop) (hb : ∀ x, B x → A x)
    (hw : WellOrderOn B R) (x y : σ) (α γ : OrdinalCarrier σ)
    (hx : RankGraph B R x α) (hy : RankGraph B R y γ) (hxy : R x y) : HartogsOrder A α γ := by
  have hseg := wellOrder_restrict B (Segment B R y) R hw (fun _ h => h.1)
  obtain ⟨F,hf⟩ := nested_segment_iso B R hw y x hy.1 ⟨hx.1,hxy⟩
  have he := (exactOrdinal_iso α hx.2.1 _ _ _ _ F
    (wellOrder_restrict _ _ _ hseg (fun _ h => h.1))
    (wellOrder_restrict B _ R hw (fun _ h => h.1)) hf).mpr hx.2.2
  exact ⟨rank_hartogs A B R hb hw x α hx,rank_hartogs A B R hb hw y γ hy,
    RestrictOrder R (Segment B R y),Segment B R y,fun z hz => hb z hz.1,hseg,hy.2.2,x,⟨hx.1,hxy⟩,he⟩

theorem rank_injective (B : σ → Prop) (R : σ → σ → Prop) (hw : WellOrderOn B R) :
    ∀ x z α, RankGraph B R x α → RankGraph B R z α → x = z := by
  intro x z α hx hz
  obtain he | hxz | hzx := hw.1.2.2.2 x z hx.1 hz.1
  · exact he
  · exact (hartogsOrder_irrefl B α (rank_increasing B B R (fun _ h => h) hw x z α α hx hz hxz)).elim
  · exact (hartogsOrder_irrefl B α (rank_increasing B B R (fun _ h => h) hw z x α α hz hx hzx)).elim

theorem rank_functional (B : σ → Prop) (R : σ → σ → Prop) :
    ∀ x α γ, RankGraph B R x α → RankGraph B R x γ → α = γ :=
  fun x α γ hx hy => exact_ordinal_unique α γ hx.2.1 hy.2.1 _ _ hx.2.2 hy.2.2

theorem rank_below (A B : σ → Prop) (R : σ → σ → Prop) (hb : ∀ x, B x → A x)
    (hw : WellOrderOn B R) (β : OrdinalCarrier σ) (hβ : Ordinal β) (he : ExactOrdinal β R B)
    (x : σ) (α : OrdinalCarrier σ) (hx : RankGraph B R x α) :
    Segment (HartogsCarrier A) (HartogsOrder A) β α :=
  ⟨rank_hartogs A B R hb hw x α hx,rank_hartogs A B R hb hw x α hx,
    ⟨hβ,R,B,hb,hw,he⟩,R,B,hb,hw,he,x,hx.1,hx.2.2⟩

theorem rank_maps (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A B : σ → Prop) (R : σ → σ → Prop) (hb : ∀ x, B x → A x)
    (hw : WellOrderOn B R) (β : OrdinalCarrier σ) (hβ : Ordinal β) (he : ExactOrdinal β R B) :
    Maps (RankGraph B R) B (Segment (HartogsCarrier A) (HartogsOrder A) β) := by
  refine ⟨fun x α hx => ⟨hx.1,rank_below A B R hb hw β hβ he x α hx⟩,?_,rank_functional B R⟩
  intro x hx
  obtain ⟨α,hα,ha⟩ := exact_ordinal_exists rc (Segment B R x) (RestrictOrder R (Segment B R x))
    (wellOrder_restrict B _ R hw (fun _ h => h.1))
  exact ⟨α,rank_below A B R hb hw β hβ he x α ⟨hx,hα,ha⟩,hx,hα,ha⟩

theorem rank_onto (A B : σ → Prop) (R : σ → σ → Prop)
    (β : OrdinalCarrier σ) (he : ExactOrdinal β R B)
    (α : OrdinalCarrier σ) (hα : Segment (HartogsCarrier A) (HartogsOrder A) β α) :
    ∃ x, B x ∧ RankGraph B R x α := by
  have hs := box_elim (hartogs_lt_implies A α β hα.2) R B he.1
  obtain ⟨x,hx,hax⟩ := ordinal_exact_segment α hα.1.1 B R hs
  exact ⟨x,hx,hx,hα.1.1,hax⟩

theorem rank_order_iff (A B : σ → Prop) (R : σ → σ → Prop)
    (hb : ∀ x, B x → A x) (hw : WellOrderOn B R)
    (x y : σ) (α γ : OrdinalCarrier σ) (hx : RankGraph B R x α) (hy : RankGraph B R y γ) :
    R x y ↔ HartogsOrder A α γ := by
  constructor
  · exact rank_increasing A B R hb hw x y α γ hx hy
  · intro hlt
    obtain heq | hxy | hyx := hw.1.2.2.2 x y hx.1 hy.1
    · have hsame : RankGraph B R x γ := heq.symm ▸ hy
      have hag := rank_functional B R x α γ hx hsame
      have haa : HartogsOrder A α α := Eq.mp (congrArg (fun q => HartogsOrder A α q) hag.symm) hlt
      exact (hartogsOrder_irrefl A α haa).elim
    · exact hxy
    · exact (hartogsOrder_irrefl A α (hartogs_lt_trans A α γ α hlt
        (rank_increasing A B R hb hw y x γ α hy hx hyx))).elim

theorem rank_iso (rc : P.RigidComprehension (OrdinalCarrier σ → Prop))
    (A B : σ → Prop) (R : σ → σ → Prop) (hb : ∀ x, B x → A x)
    (hw : WellOrderOn B R) (β : OrdinalCarrier σ) (hβ : Ordinal β) (he : ExactOrdinal β R B) :
    OrderIso (RankGraph B R) B R
      (Segment (HartogsCarrier A) (HartogsOrder A) β)
      (RestrictOrder (HartogsOrder A) (Segment (HartogsCarrier A) (HartogsOrder A) β)) := by
  have hm := rank_maps rc A B R hb hw β hβ he
  refine ⟨⟨⟨hm,rank_injective B R hw⟩,hm,rank_onto A B R β he⟩,?_⟩
  intro x y α γ hx hy
  exact ⟨fun h => ⟨rank_below A B R hb hw β hβ he x α hx,
    rank_below A B R hb hw β hβ he y γ hy,(rank_order_iff A B R hb hw x y α γ hx hy).mp h⟩,
    fun h => (rank_order_iff A B R hb hw x y α γ hx hy).mpr h.2.2⟩
#classicism_check exactOrdinal_iso ordinal_exact_segment hartogs_lt_implies hartogs_lt_of_suc hartogs_lt_of_implies
  hartogs_lt_trans hartogs_trichotomy hartogs_strictOrder rank_hartogs rank_increasing rank_injective rank_functional
  rank_below rank_maps rank_onto rank_order_iff rank_iso
#classicism_types exactOrdinal_iso ordinal_exact_segment hartogs_lt_implies hartogs_lt_of_suc hartogs_lt_of_implies
  hartogs_lt_trans hartogs_trichotomy hartogs_strictOrder rank_hartogs rank_increasing rank_injective rank_functional
  rank_below rank_maps rank_onto rank_order_iff rank_iso
end Classicism.MathematicalContingency
