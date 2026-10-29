import Classicism.Results.MathematicalContingency.CarrierTheory
/-! Inductive order types, not quotient classes. OpenAI Codex, prompted by Andrew Bacon. -/
namespace Classicism.MathematicalContingency
abbrev OrdinalCarrier (σ : Type) := (σ → σ → Prop) → (σ → Prop) → Prop
variable {σ : Type} [Ty σ]
def OrdZero (σ : Type) [Ty σ] : OrdinalCarrier σ := fun R A => WellOrderOn A R
def OrdSuc (α : OrdinalCarrier σ) : OrdinalCarrier σ := fun R A =>
  WellOrderOn A R ∧ ∃ a, A a ∧ α (RestrictOrder R (Segment A R a)) (Segment A R a)
def OrdLim (Y : OrdinalCarrier σ → Prop) : OrdinalCarrier σ := fun R A =>
  WellOrderOn A R ∧ ∀ β, Y β → β R A
def OrdClosed (Z : OrdinalCarrier σ → Prop) : Prop :=
  Z (OrdZero σ) ∧ (∀ α, Z α → Z (OrdSuc α)) ∧
    ∀ Y, Rigid Y → (∀ β, Y β → Z β) → Z (OrdLim Y)
def Ordinal (α : OrdinalCarrier σ) : Prop := ∀ Z, OrdClosed Z → Z α
def ExactOrdinal (α : OrdinalCarrier σ) (R : σ → σ → Prop) (A : σ → Prop) : Prop :=
  α R A ∧ ¬ OrdSuc α R A

theorem ordinal_zero : Ordinal (OrdZero σ) := fun _ h => h.1
theorem ordinal_suc (α : OrdinalCarrier σ) (h : Ordinal α) : Ordinal (OrdSuc α) :=
  fun Z hz => hz.2.1 α (h Z hz)
theorem ordinal_lim (Y : OrdinalCarrier σ → Prop) (hy : Rigid Y)
    (h : ∀ β, Y β → Ordinal β) : Ordinal (OrdLim Y) :=
  fun Z hz => hz.2.2 Y hy (fun β hb => h β hb Z hz)
theorem ordinal_induction (P : OrdinalCarrier σ → Prop) (hz : P (OrdZero σ))
    (hs : ∀ α, Ordinal α → P α → P (OrdSuc α))
    (hl : ∀ Y, Rigid Y → (∀ β, Y β → Ordinal β ∧ P β) → P (OrdLim Y))
    (α : OrdinalCarrier σ) (hα : Ordinal α) : P α :=
  (hα (fun β => Ordinal β ∧ P β) ⟨⟨ordinal_zero,hz⟩,
    (fun β h => ⟨ordinal_suc β h.1,hs β h.1 h.2⟩),
    fun Y hy h => ⟨ordinal_lim Y hy (fun β hb => (h β hb).1),hl Y hy h⟩⟩).2

theorem ordinal_implies_wellOrder (α : OrdinalCarrier σ) (hα : Ordinal α) :
    ∀ R A, α R A → WellOrderOn A R :=
  ordinal_induction (fun α => ∀ R A, α R A → WellOrderOn A R) (fun _ _ h => h) (fun _ _ _ _ _ h => h.1)
    (fun _ _ _ _ _ h => h.1) α hα

theorem ordinal_necessarily_wellOrder (α : OrdinalCarrier σ) (hα : Ordinal α) :
    □ (∀ R A, α R A → WellOrderOn A R) :=
  ordinal_induction (fun α => □ (∀ R A, α R A → WellOrderOn A R)) (nec% (fun R A (h : OrdZero σ R A) => h))
    (fun β _ _ => nec% (fun R A (h : OrdSuc β R A) => h.1))
    (fun Y _ _ => nec% (fun R A (h : OrdLim Y R A) => h.1)) α hα

theorem exactOrdinal_wellOrder (α : OrdinalCarrier σ) (hα : Ordinal α)
    (R : σ → σ → Prop) (A : σ → Prop) (h : ExactOrdinal α R A) : WellOrderOn A R :=
  ordinal_implies_wellOrder α hα R A h.1

theorem ordSuc_witness (α : OrdinalCarrier σ) (R : σ → σ → Prop) (A : σ → Prop)
    (h : OrdSuc α R A) : ∃ a, A a ∧ α (RestrictOrder R (Segment A R a)) (Segment A R a) := h.2

theorem exactOrdZero_iff_empty (R : σ → σ → Prop) (A : σ → Prop) :
    ExactOrdinal (OrdZero σ) R A ↔ (WellOrderOn A R ∧ ∀ x, ¬ A x) := by
  constructor
  · intro h; refine ⟨h.1,?_⟩
    intro x hx
    exact h.2 ⟨h.1,x,hx,wellOrder_restrict A _ R h.1 (fun _ h => h.1)⟩
  · intro h; exact ⟨h.1,fun hs => hs.2.elim fun x hx => h.2 x hx.1⟩

def HartogsCarrier (A : σ → Prop) (α : OrdinalCarrier σ) : Prop :=
  Ordinal α ∧ ∃ R B, (∀ x, B x → A x) ∧ WellOrderOn B R ∧ ExactOrdinal α R B

def HartogsOrder (A : σ → Prop) (α β : OrdinalCarrier σ) : Prop :=
  HartogsCarrier A α ∧ HartogsCarrier A β ∧ ∃ R B, (∀ x, B x → A x) ∧
    WellOrderOn B R ∧ ExactOrdinal β R B ∧ ∃ b, B b ∧
      ExactOrdinal α (RestrictOrder R (Segment B R b)) (Segment B R b)

theorem hartogsCarrier_mono (A B : σ → Prop) (h : ∀ x, A x → B x)
    (α : OrdinalCarrier σ) (ha : HartogsCarrier A α) : HartogsCarrier B α := by
  obtain ⟨hα,R,D,hd,hw,he⟩ := ha
  exact ⟨hα,R,D,fun x hx => h x (hd x hx),hw,he⟩
theorem empty_wellOrder : WellOrderOn (fun _ : σ => False) (fun _ _ => False) :=
  ⟨⟨fun _ _ h => h.elim,fun _ h => h.elim,fun _ _ _ h => h.elim,fun _ _ h => h.elim⟩,
    fun X hx he => he.elim fun x h => (hx x h).elim⟩
theorem hartogsCarrier_zero (A : σ → Prop) : HartogsCarrier A (OrdZero σ) :=
  ⟨ordinal_zero,fun _ _ => False,fun _ => False,fun _ h => h.elim,empty_wellOrder,
    (exactOrdZero_iff_empty _ _).mpr ⟨empty_wellOrder,fun _ h => h⟩⟩

theorem ordLim_eq_zero (Y : OrdinalCarrier σ → Prop) (hy : Rigid Y)
    (hz : ∀ β, Y β → β = OrdZero σ) : OrdLim Y = OrdZero σ := by
  have hb := restricted_barcan_unary Y (fun β => β = OrdZero σ) hy
    (fun β hβ => necessity_of_identity β (OrdZero σ) (hz β hβ))
  exact intensionality _ _ (modal_K _ _
    (nec% (fun (h : ∀ β, Y β → β = OrdZero σ) R A =>
      (show OrdLim Y R A ↔ OrdZero σ R A from
        ⟨fun hh => hh.1,fun hh => ⟨hh,fun β hβ => (h β hβ).symm ▸ hh⟩⟩))) hb)

theorem ordinal_empty_unique (α : OrdinalCarrier σ) (hα : Ordinal α) :
    ∀ R A, (∀ x, ¬ A x) → α R A → α = OrdZero σ := by
  apply ordinal_induction _ (fun _ _ _ _ => rfl) ?_ ?_ α hα
  · intro β _ _ R A he hs
    exact (hs.2.elim fun a ha => he a ha.1).elim
  · intro Y hy ih R A he h
    exact ordLim_eq_zero Y hy (fun β hβ => (ih β hβ).2 R A he (h.2 β hβ))

theorem hartogs_empty_iff_zero (α : OrdinalCarrier σ) :
    HartogsCarrier (fun _ : σ => False) α ↔ α = OrdZero σ := by
  constructor
  · intro h
    obtain ⟨R,B,hb,_,he⟩ := h.2
    exact ordinal_empty_unique α h.1 R B (fun x hx => hb x hx) he.1
  · intro h; exact h.symm ▸ hartogsCarrier_zero (fun _ : σ => False)

#classicism_check ordinal_zero ordinal_suc ordinal_lim ordinal_induction ordinal_implies_wellOrder
  ordinal_necessarily_wellOrder exactOrdinal_wellOrder ordSuc_witness exactOrdZero_iff_empty
  hartogsCarrier_mono empty_wellOrder hartogsCarrier_zero ordLim_eq_zero ordinal_empty_unique hartogs_empty_iff_zero
#classicism_types ordinal_zero ordinal_suc ordinal_lim ordinal_induction ordinal_implies_wellOrder
  ordinal_necessarily_wellOrder exactOrdinal_wellOrder ordSuc_witness exactOrdZero_iff_empty
  hartogsCarrier_mono empty_wellOrder hartogsCarrier_zero ordLim_eq_zero ordinal_empty_unique hartogs_empty_iff_zero
end Classicism.MathematicalContingency
