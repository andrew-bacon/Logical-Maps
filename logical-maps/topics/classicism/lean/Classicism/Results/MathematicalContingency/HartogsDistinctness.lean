import Classicism.Results.MathematicalContingency.OrdinalStability
import Classicism.Results.MathematicalContingency.HartogsRanks
import Classicism.Results.MathematicalContingency.NaturalModal

/-! Necessary distinctness of the currently realized Hartogs types.
OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
Only domain-relative ND and the displayed current RC instances are used. -/
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]

theorem wellOrder_coext (A B : σ → Prop) (R S : σ → σ → Prop)
    (hw : WellOrderOn A R) (hc : ∀ x, A x ↔ B x) (hr : ∀ x y, R x y ↔ S x y) :
    WellOrderOn B S := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro x y h
    have hd := hw.1.1 x y ((hr x y).mpr h)
    exact ⟨(hc x).mp hd.1,(hc y).mp hd.2⟩
  · intro x hx h; exact hw.1.2.1 x ((hc x).mpr hx) ((hr x x).mpr h)
  · intro x y z hx hy hz hxy hyz
    exact (hr x z).mp (hw.1.2.2.1 x y z ((hc x).mpr hx) ((hc y).mpr hy)
      ((hc z).mpr hz) ((hr x y).mpr hxy) ((hr y z).mpr hyz))
  · intro x y hx hy
    obtain e | h | h := hw.1.2.2.2 x y ((hc x).mpr hx) ((hc y).mpr hy)
    · exact Or.inl e
    · exact Or.inr (Or.inl ((hr x y).mp h))
    · exact Or.inr (Or.inr ((hr y x).mp h))
  · intro X hX he
    obtain ⟨x,hx,hm⟩ := hw.2 X (fun y hy => (hc y).mpr (hX y hy)) he
    exact ⟨x,hx,fun y hy h => hm y hy ((hr y x).mpr h)⟩

theorem exactOrdinal_rigid_realization
    (rcF : P.RigidComprehension (σ → Prop))
    (rcR : P.RigidComprehension (σ → σ → Prop))
    (D : σ → Prop) (nd : DomainND D) (α : OrdinalCarrier σ)
    (hα : HartogsCarrier D α) :
    ∃ B S, (∀ x, B x → D x) ∧ Rigid B ∧ Rigid S ∧ StableOrder B S ∧ ExactOrdinal α S B := by
  obtain ⟨ho,R,A,ha,hw,he⟩ := hα
  obtain ⟨B,hB,eB⟩ := rcF A
  obtain ⟨S,hS,eS⟩ := rcR R
  have hb : ∀ x, B x → D x := fun x hx => ha x ((eB x).mpr hx)
  have hs := wellOrder_coext A B R S hw eB eS
  have hi := orderIso_of_coext A B R S eB (fun x y _ _ => eS x y)
  exact ⟨B,S,hb,hB,hS,rigid_wellOrder_stable B S hs hB hS
    (fun x y hx hy => nd x y (hb x hx) (hb y hy)),
    (exactOrdinal_iso α ho A B R S _ hw hs hi).mp he⟩

/-- One stable exact realization distinguishes its type from every other current ordinal. -/
theorem stable_exactOrdinal_distinct (α β : OrdinalCarrier σ)
    (hα : Ordinal α) (hβ : Ordinal β)
    (A : σ → Prop) (R : σ → σ → Prop) (hs : StableOrder A R)
    (he : ExactOrdinal α R A) (hne : α ≠ β) : □ (α ≠ β) := by
  obtain hb | hb := em (β R A)
  · have hsb : OrdSuc β R A := (em (OrdSuc β R A)).elim id
      (fun hn => (hne (exact_ordinal_unique α β hα hβ A R he ⟨hb,hn⟩)).elim)
    exact modal_K _ _ (modal_K _ _
      (nec% (fun (hn : ¬ OrdSuc α R A) (hp : OrdSuc β R A) (e : α = β) => hn (e.symm ▸ hp)))
      (ordinal_application_negative (OrdSuc α) (ordinal_suc α hα) A R hs he.2))
      (ordinal_application_persistent (OrdSuc β) (ordinal_suc β hβ) A R hs hsb)
  · exact modal_K _ _ (modal_K _ _
      (nec% (fun (hp : α R A) (hn : ¬ β R A) (e : α = β) => hn (e ▸ hp)))
      (ordinal_application_persistent α hα A R hs he.1))
      (ordinal_application_negative β hβ A R hs hb)

theorem hartogsCarrier_nd
    (rcF : P.RigidComprehension (σ → Prop))
    (rcR : P.RigidComprehension (σ → σ → Prop))
    (D : σ → Prop) (nd : DomainND D) : DomainND (HartogsCarrier D) := by
  intro α β hα hβ hne
  obtain ⟨B,S,_,_,_,hs,he⟩ := exactOrdinal_rigid_realization rcF rcR D nd α hα
  exact stable_exactOrdinal_distinct α β hα.1 hβ.1 B S hs he hne

/-- This ND result does not require the deferred rigidity of LowerNat. -/
theorem natural_hartogs_nd (hi : DraftBoxInfinity σ)
    (rcF : P.RigidComprehension (((σ → Prop) → Prop) → Prop))
    (rcR : P.RigidComprehension (((σ → Prop) → Prop) → ((σ → Prop) → Prop) → Prop)) :
    DomainND (HartogsCarrier (@LowerNat σ _)) :=
  hartogsCarrier_nd rcF rcR LowerNat (fun m n hm hn => lowerNat_nd hi m n hm hn)

#classicism_check wellOrder_coext exactOrdinal_rigid_realization stable_exactOrdinal_distinct
  hartogsCarrier_nd natural_hartogs_nd
#classicism_types wellOrder_coext exactOrdinal_rigid_realization stable_exactOrdinal_distinct
  hartogsCarrier_nd natural_hartogs_nd
end Classicism.MathematicalContingency
