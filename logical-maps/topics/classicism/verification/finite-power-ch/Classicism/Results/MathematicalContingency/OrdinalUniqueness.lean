import Classicism.Results.MathematicalContingency.OrdinalExistence
/-! Exact-type uniqueness by separation at proper segments.
OpenAI Codex, prompted by Andrew Bacon, reconstructed 25 October 2026. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]
def OrdImplies (α β : OrdinalCarrier σ) : Prop := ∀ R A, α R A → β R A
def SeparatesAt (A : σ → Prop) (R : σ → σ → Prop) : Prop :=
  ∀ α β, Ordinal α → Ordinal β → α R A → ¬ β R A → □ (OrdImplies β (OrdSuc α))
def BoundsAt (A : σ → Prop) (R : σ → σ → Prop) : Prop :=
  ∀ α β, Ordinal α → Ordinal β → α R A →
    (∀ a, A a → ¬ β (RestrictOrder R (Segment A R a)) (Segment A R a)) → □ (OrdImplies β α)
theorem ordImplies_suc (α β : OrdinalCarrier σ) (h : OrdImplies α β) :
    OrdImplies (OrdSuc α) (OrdSuc β) := fun R A hs =>
  ⟨hs.1,hs.2.elim fun a ha => ⟨a,ha.1,h _ _ ha.2⟩⟩
theorem ordImplies_trans (α β γ : OrdinalCarrier σ)
    (h : OrdImplies α β) (k : OrdImplies β γ) : OrdImplies α γ := fun R A ha => k R A (h R A ha)
theorem ordImplies_lim (Y : OrdinalCarrier σ → Prop) (β : OrdinalCarrier σ)
    (hw : OrdImplies β (OrdZero σ)) (h : ∀ γ, Y γ → OrdImplies β γ) :
    OrdImplies β (OrdLim Y) := fun R A hb => ⟨hw R A hb,fun γ hγ => h γ hγ R A hb⟩
theorem bounds_of_segment_separation (A : σ → Prop) (R : σ → σ → Prop)
    (hseg : ∀ a, A a → SeparatesAt (Segment A R a) (RestrictOrder R (Segment A R a))) :
    BoundsAt A R := by
  intro α β hα hβ
  apply ordinal_induction (fun α => α R A →
    (∀ a, A a → ¬ β (RestrictOrder R (Segment A R a)) (Segment A R a)) → □ (OrdImplies β α))
    ?_ ?_ ?_ α hα
  · intro _ _
    exact ordinal_necessarily_wellOrder β hβ
  · intro γ hγ _ hs hn
    obtain ⟨a,ha,hγa⟩ := hs.2
    exact hseg a ha γ β hγ hβ hγa (hn a ha)
  · intro Y hy ih h hn
    have hb := restricted_barcan_unary Y (fun γ => OrdImplies β γ) hy
      (fun γ hγ => (ih γ hγ).2 (h.2 γ hγ) hn)
    exact modal_K _ _ (modal_K _ _ (nec% (ordImplies_lim Y β))
      (ordinal_necessarily_wellOrder β hβ)) hb
theorem separation_of_bounds (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) (hb : BoundsAt A R) : SeparatesAt A R := by
  intro α β hα hβ ha
  apply ordinal_induction (fun β => ¬ β R A → □ (OrdImplies β (OrdSuc α))) ?_ ?_ ?_ β hβ
  · intro hn; exact (hn hw).elim
  · intro γ hγ _ hn
    have hno : ∀ a, A a → ¬ γ (RestrictOrder R (Segment A R a)) (Segment A R a) :=
      fun a ha h => hn ⟨hw,a,ha,h⟩
    exact modal_K _ _ (nec% (ordImplies_suc γ α)) (hb α γ hα hγ ha hno)
  · intro Y hy ih hn
    have hex : ∃ γ, Y γ ∧ ¬ γ R A := by
      refine (em (∃ γ, Y γ ∧ ¬ γ R A)).elim (fun h => h) ?_
      intro h
      exact (hn ⟨hw,fun γ hγ => (em (γ R A)).elim (fun h => h)
        (fun hn => (h ⟨γ,hγ,hn⟩).elim)⟩).elim
    obtain ⟨γ,hγ,hnγ⟩ := hex
    have hleft : □ (OrdImplies (OrdLim Y) γ) := modal_K _ _
      (nec% (fun (hyγ : Y γ) S B (h : OrdLim Y S B) => h.2 γ hyγ))
      (box_elim hy.1 γ hγ)
    exact modal_K _ _ (modal_K _ _ (nec% (ordImplies_trans (OrdLim Y) γ (OrdSuc α)))
      hleft) ((ih γ hγ).2 hnγ)
theorem separates_of_iso (A B : σ → Prop) (R S : σ → σ → Prop) (F : σ → σ → Prop)
    (hw : WellOrderOn A R) (hs : WellOrderOn B S) (hf : OrderIso F A R B S)
    (h : SeparatesAt A R) : SeparatesAt B S := by
  intro α β hα hβ ha hn
  have hi := upward_iso_iff α (ordinal_upward α hα) A B R S F hw hs hf
  have hj := upward_iso_iff β (ordinal_upward β hβ) A B R S F hw hs hf
  exact h α β hα hβ (hi.mpr ha) (fun hβa => hn (hj.mp hβa))
theorem wellOrder_segment_separation (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) :
    ∀ a, A a → SeparatesAt (Segment A R a) (RestrictOrder R (Segment A R a)) := by
  apply wellOrder_induction A R hw (fun a => SeparatesAt (Segment A R a) (RestrictOrder R (Segment A R a)))
  intro a ha ih
  have hwa := wellOrder_restrict A (Segment A R a) R hw (fun _ h => h.1)
  apply separation_of_bounds _ _ hwa
  apply bounds_of_segment_separation
  intro b hb
  obtain ⟨F,hf⟩ := nested_segment_iso A R hw a b ha hb
  have hwb := wellOrder_restrict A (Segment A R b) R hw (fun _ h => h.1)
  have hwn := wellOrder_restrict (Segment A R a)
    (Segment (Segment A R a) (RestrictOrder R (Segment A R a)) b) _ hwa (fun _ h => h.1)
  exact separates_of_iso _ _ _ _ (fun y x => F x y) hwb hwn
    (orderIso_inverse _ _ _ _ F hf) (ih b hb.1 hb.2)
theorem wellOrder_bounds (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) : BoundsAt A R :=
  bounds_of_segment_separation A R (wellOrder_segment_separation A R hw)
theorem wellOrder_separation (A : σ → Prop) (R : σ → σ → Prop)
    (hw : WellOrderOn A R) : SeparatesAt A R :=
  separation_of_bounds A R hw (wellOrder_bounds A R hw)
theorem exact_ordinal_unique (α β : OrdinalCarrier σ) (hα : Ordinal α) (hβ : Ordinal β)
    (A : σ → Prop) (R : σ → σ → Prop)
    (ha : ExactOrdinal α R A) (hb : ExactOrdinal β R A) : α = β := by
  have hw := exactOrdinal_wellOrder α hα R A ha
  have hαno : ∀ a, A a → ¬ α (RestrictOrder R (Segment A R a)) (Segment A R a) :=
    fun a h h' => ha.2 ⟨hw,a,h,h'⟩
  have hβno : ∀ a, A a → ¬ β (RestrictOrder R (Segment A R a)) (Segment A R a) :=
    fun a h h' => hb.2 ⟨hw,a,h,h'⟩
  have h1 := wellOrder_bounds A R hw β α hβ hα hb.1 hαno
  have h2 := wellOrder_bounds A R hw α β hα hβ ha.1 hβno
  exact intensionality α β (modal_K _ _ (modal_K _ _
    (nec% (fun (h : OrdImplies α β) (k : OrdImplies β α) S B =>
      (show α S B ↔ β S B from ⟨h S B,k S B⟩))) h1) h2)
#classicism_check ordImplies_suc ordImplies_trans ordImplies_lim bounds_of_segment_separation
  separation_of_bounds separates_of_iso wellOrder_segment_separation wellOrder_bounds
  wellOrder_separation exact_ordinal_unique
#classicism_types ordImplies_suc ordImplies_trans ordImplies_lim bounds_of_segment_separation
  separation_of_bounds separates_of_iso wellOrder_segment_separation wellOrder_bounds
  wellOrder_separation exact_ordinal_unique
end Classicism.MathematicalContingency
