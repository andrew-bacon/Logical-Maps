import Classicism.Results.MathematicalContingency.StableOrderSegments
import Classicism.Results.MathematicalContingency.InductiveOrdinals

/-! Applications of current inductive order types to stable well-orders are decided.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
No necessary distinctness of ordinal properties is assumed. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def OrdinalStableApplication (α : OrdinalCarrier σ) : Prop :=
  ∀ A R, StableOrder A R → □ (α R A) ∨ □ (¬ α R A)

theorem ordZero_stableApplication : OrdinalStableApplication (OrdZero σ) :=
  fun _ _ h => Or.inl h.1

theorem ordSuc_stableApplication (α : OrdinalCarrier σ)
    (ih : OrdinalStableApplication α) : OrdinalStableApplication (OrdSuc α) := by
  intro A R h
  obtain he | hn := em (∃ a, A a ∧ α (RestrictOrder R (Segment A R a)) (Segment A R a))
  · obtain ⟨a,ha,hα⟩ := he
    have hb : □ (α (RestrictOrder R (Segment A R a)) (Segment A R a)) :=
      (ih _ _ (stableOrder_segment A R h a ha)).elim id (fun hn => (box_elim hn hα).elim)
    exact Or.inl (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (hw : WellOrderOn A R) (ha : A a)
        (hb : α (RestrictOrder R (Segment A R a)) (Segment A R a)) =>
        (show OrdSuc α R A from ⟨hw,a,ha,hb⟩))) h.1) (h.2.1.1 a ha)) hb)
  · have hb : □ (∀ a, A a → ¬ α (RestrictOrder R (Segment A R a)) (Segment A R a)) :=
      h.2.1.2 (fun a => ¬ α (RestrictOrder R (Segment A R a)) (Segment A R a)) (by
        intro a ha
        exact (ih _ _ (stableOrder_segment A R h a ha)).elim
          (fun hp => (hn ⟨a,ha,box_elim hp⟩).elim) id)
    exact Or.inr (modal_K _ _ (nec% (fun
      (hb : ∀ a, A a → ¬ α (RestrictOrder R (Segment A R a)) (Segment A R a))
      (hs : OrdSuc α R A) => hs.2.elim fun a ha => hb a ha.1 ha.2)) hb)

theorem ordLim_stableApplication (Y : OrdinalCarrier σ → Prop) (hy : Rigid Y)
    (ih : ∀ α, Y α → OrdinalStableApplication α) : OrdinalStableApplication (OrdLim Y) := by
  intro A R h
  obtain he | hn := em (∃ α, Y α ∧ ¬ α R A)
  · obtain ⟨α,hα,hnot⟩ := he
    have hb : □ (¬ α R A) := (ih α hα A R h).elim (fun hp => (hnot (box_elim hp)).elim) id
    exact Or.inr (modal_K _ _ (modal_K _ _
      (nec% (fun (hyα : Y α) (hnα : ¬ α R A) (hl : OrdLim Y R A) => hnα (hl.2 α hyα)))
      (box_elim hy.1 α hα)) hb)
  · have hb : □ (∀ α, Y α → α R A) := restricted_barcan_unary Y (fun α => α R A) hy (by
      intro α hα
      exact (ih α hα A R h).elim id (fun hnα => (hn ⟨α,hα,box_elim hnα⟩).elim))
    exact Or.inl (modal_K _ _ (modal_K _ _
      (nec% (fun (hw : WellOrderOn A R) (hb : ∀ α, Y α → α R A) =>
        (show OrdLim Y R A from ⟨hw,hb⟩))) h.1) hb)

theorem ordinal_stableApplication (α : OrdinalCarrier σ) (hα : Ordinal α) :
    OrdinalStableApplication α :=
  ordinal_induction OrdinalStableApplication ordZero_stableApplication
    (fun β _ ih => ordSuc_stableApplication β ih)
    (fun Y hy ih => ordLim_stableApplication Y hy (fun β hb => (ih β hb).2)) α hα

theorem ordinal_application_persistent (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A : σ → Prop) (R : σ → σ → Prop) (hs : StableOrder A R)
    (h : α R A) : □ (α R A) :=
  (ordinal_stableApplication α hα A R hs).elim id (fun hn => (box_elim hn h).elim)

theorem ordinal_application_negative (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A : σ → Prop) (R : σ → σ → Prop) (hs : StableOrder A R)
    (h : ¬ α R A) : □ (¬ α R A) :=
  (ordinal_stableApplication α hα A R hs).elim (fun hp => (h (box_elim hp)).elim) id

theorem ordinal_rigid_application_stable (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A : σ → Prop) (R : σ → σ → Prop) (hw : WellOrderOn A R)
    (ha : Rigid A) (hr : Rigid R) (nd : DomainND A) :
    (α R A → □ (α R A)) ∧ (¬ α R A → □ (¬ α R A)) :=
  ⟨ordinal_application_persistent α hα A R (rigid_wellOrder_stable A R hw ha hr nd),
   ordinal_application_negative α hα A R (rigid_wellOrder_stable A R hw ha hr nd)⟩

theorem exactOrdinal_stable (α : OrdinalCarrier σ) (hα : Ordinal α)
    (A : σ → Prop) (R : σ → σ → Prop) (hs : StableOrder A R)
    (he : ExactOrdinal α R A) : □ (ExactOrdinal α R A) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (hp : α R A) (hn : ¬ OrdSuc α R A) =>
      (show ExactOrdinal α R A from ⟨hp,hn⟩)))
    (ordinal_application_persistent α hα A R hs he.1))
    (ordinal_application_negative (OrdSuc α) (ordinal_suc α hα) A R hs he.2)

#classicism_check ordZero_stableApplication ordSuc_stableApplication ordLim_stableApplication
  ordinal_stableApplication ordinal_application_persistent ordinal_application_negative
  ordinal_rigid_application_stable exactOrdinal_stable
#classicism_types ordZero_stableApplication ordSuc_stableApplication ordLim_stableApplication
  ordinal_stableApplication ordinal_application_persistent ordinal_application_negative
  ordinal_rigid_application_stable exactOrdinal_stable
end Classicism.MathematicalContingency
