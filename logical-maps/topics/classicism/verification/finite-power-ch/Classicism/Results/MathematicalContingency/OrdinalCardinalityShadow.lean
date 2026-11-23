import Classicism.Results.MathematicalContingency.WellOrderAdjoinTop

/-! The cardinality property induced by an inexact order property.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026.
Identities below come from NECESSARY coextension, not actual coextension.
-/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

def OrdinalCard (α : OrdinalCarrier σ) (F : σ → Prop) : Prop :=
  ∃ A R, (∀ x, A x → F x) ∧ WellOrderOn A R ∧ α R A

theorem ordinalCard_zero_of_empty (F A : σ → Prop) (R : σ → σ → Prop)
    (empty : ∀ x, ¬ A x) (hw : WellOrderOn A R) : OrdinalCard (OrdZero σ) F :=
  ⟨A,R,(fun x h => (empty x h).elim),hw,hw⟩

theorem exists_empty_wellOrder :
    ∃ (A : σ → Prop) (R : σ → σ → Prop), (∀ x, ¬ A x) ∧ WellOrderOn A R := by
  refine ⟨(fun x => x ≠ x),(fun x y => x ≠ x ∧ y ≠ y),
    (fun x h => h rfl),⟨?_,?_⟩⟩
  · exact ⟨fun _ _ h => h,fun _ hx _ => hx rfl,
      fun _ _ _ hx _ _ _ _ => (hx rfl).elim,
      fun _ _ hx _ => (hx rfl).elim⟩
  · intro X sub inhabited
    exact inhabited.elim (fun x hx => ((sub x hx) rfl).elim)

theorem ordinalCard_zero_coext :
    ∀ F : σ → Prop, OrdinalCard (OrdZero σ) F ↔ AtLeastZero σ F := by
  obtain ⟨A,R,empty,hw⟩ := @exists_empty_wellOrder σ _
  intro F
  exact ⟨fun _ => trivial,fun _ => ordinalCard_zero_of_empty F A R empty hw⟩

theorem ordinalCard_zero : OrdinalCard (OrdZero σ) = AtLeastZero σ :=
  intensionality _ _ (nec% (@ordinalCard_zero_coext σ _))

theorem ordinalCard_suc_coext (α : OrdinalCarrier σ) (upward : UpwardOrdinal α) :
    ∀ F : σ → Prop, OrdinalCard (OrdSuc α) F ↔ SucCard (OrdinalCard α) F := by
  intro F
  constructor
  · intro ⟨A,R,sub,hw,_,a,ha,hα⟩
    refine ⟨a,sub a ha,Segment A R a,RestrictOrder R (Segment A R a),?_,
      wellOrder_restrict A _ R hw (fun _ h => h.1),hα⟩
    intro x hx
    exact ⟨sub x hx.1,fun e => hw.1.2.1 a ha (e ▸ hx.2)⟩
  · intro ⟨a,ha,A,R,sub,hw,hα⟩
    have fresh : ¬ A a := fun h => (sub a h).2 rfl
    have hW := adjoinTop_wellOrder A R a hw fresh
    have hseg := wellOrder_restrict (AdjoinTopCarrier A a)
      (Segment (AdjoinTopCarrier A a) (AdjoinTopOrder A R a) a)
      (AdjoinTopOrder A R a) hW (fun _ h => h.1)
    refine ⟨AdjoinTopCarrier A a,AdjoinTopOrder A R a,?_,hW,hW,a,Or.inr rfl,?_⟩
    · intro x hx
      exact hx.elim (fun h => (sub x h).1) (fun e => e.symm ▸ ha)
    · exact upward _ _ _ _ _ hw hseg
        (orderIso_initial _ _ _ _ _ (adjoinTop_segment_iso A R a hw fresh)) hα

theorem ordinalCard_suc (α : OrdinalCarrier σ) (hα : Ordinal α) :
    OrdinalCard (OrdSuc α) = SucCard (OrdinalCard α) :=
  intensionality _ _ (modal_K _ _ (nec% (ordinalCard_suc_coext α))
    (ordinal_upward_necessary α hα))

#classicism_check ordinalCard_zero_of_empty exists_empty_wellOrder ordinalCard_zero_coext ordinalCard_zero ordinalCard_suc_coext ordinalCard_suc
#classicism_types ordinalCard_zero_of_empty exists_empty_wellOrder ordinalCard_zero_coext ordinalCard_zero ordinalCard_suc_coext ordinalCard_suc
end Classicism.MathematicalContingency
