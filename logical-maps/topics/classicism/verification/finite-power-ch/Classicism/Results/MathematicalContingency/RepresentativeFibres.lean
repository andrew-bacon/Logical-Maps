import Classicism.Results.MathematicalContingency.InjectionSelection
import Classicism.Results.MathematicalContingency.AntichainCounting
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β : Type} [Ty α] [Ty β]

/-- E is the frozen collection of current names; its members need not be rigid. -/
def RepresentativeImage (E : (α → Prop) → Prop) (U : α → Prop) : Prop :=
  Rigid U ∧ ∃ X, E X ∧ U ≡ X

def RepresentativeValue (Q : Prop) (J : (α → Prop) → β → Prop) (X : α → Prop) (b : β) : Prop :=
  Q ∧ ∃ U, Rigid U ∧ U ≡ X ∧ J U b

theorem rigid_representative_exists (rc : Classicism.P.RigidComprehension (α → Prop)) (X : α → Prop) :
    ∃ U, Rigid U ∧ U ≡ X := by
  obtain ⟨U,hr,hc⟩ := rc X
  exact ⟨U,hr,fun x => (hc x).symm⟩

theorem representativeValue_cover_current (E : (α → Prop) → Prop) (B : β → Prop)
    (Q : Prop) (J : (α → Prop) → β → Prop) (X : α → Prop)
    (hr : ∃ U, Rigid U ∧ U ≡ X) (hx : E X)
    (hj : Q → Injects J (RepresentativeImage E) B) (hq : Q) :
    ∃ b, B b ∧ RepresentativeValue Q J X b := by
  obtain ⟨U,hu,hUX⟩ := hr
  obtain ⟨b,hb,hJ⟩ := (hj hq).1.2.1 U ⟨hu,X,hx,hUX⟩
  exact ⟨b,hb,hq,U,hu,hUX,hJ⟩

theorem representativeValue_cover (E : (α → Prop) → Prop) (B : β → Prop)
    (Q : Prop) (J : (α → Prop) → β → Prop)
    (rc : □ (Classicism.P.RigidComprehension (α → Prop))) (he : Rigid E)
    (hj : EntailmentOrder Q (Injects J (RepresentativeImage E) B))
    (X : α → Prop) (hx : E X) :
    EntailmentOrder Q (∃ b, B b ∧ RepresentativeValue Q J X b) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (representativeValue_cover_current E B Q J X))
    (modal_K _ _ (nec% (fun h => rigid_representative_exists h X)) rc))
    (box_elim he.1 X hx)) hj

theorem representativeValue_conflict (E : (α → Prop) → Prop) (B : β → Prop)
    (Q : Prop) (J : (α → Prop) → β → Prop) (X Y : α → Prop) (b : β)
    (hj : Q → Injects J (RepresentativeImage E) B) (hs : Q → ¬ (X ≡ Y))
    (hx : RepresentativeValue Q J X b) (hy : RepresentativeValue Q J Y b) : False := by
  obtain ⟨U,hu,hUX,hU⟩ := hx.2
  obtain ⟨V,hv,hVY,hV⟩ := hy.2
  have e : U = V := (hj hx.1).2 U V b hU hV
  have hUY : U ≡ Y := e.symm ▸ hVY
  exact hs hx.1 (fun a => (hUX a).symm.trans (hUY a))

theorem representativeValue_disjoint (E : (α → Prop) → Prop) (B : β → Prop)
    (Q : Prop) (J : (α → Prop) → β → Prop) (X Y : α → Prop) (b : β)
    (hj : EntailmentOrder Q (Injects J (RepresentativeImage E) B))
    (hs : EntailmentOrder Q (¬ (X ≡ Y))) :
    □ (¬ (RepresentativeValue Q J X b ∧ RepresentativeValue Q J Y b)) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun hj hs h => representativeValue_conflict E B Q J X Y b hj hs h.1 h.2)) hj) hs

theorem representativeValue_below (P Q : Prop) (J : (α → Prop) → β → Prop)
    (hQP : EntailmentOrder Q P) (X : α → Prop) (b : β) : Below P (RepresentativeValue Q J X b) :=
  entailment_trans (RepresentativeValue Q J X b) Q P (nec% (fun h : RepresentativeValue Q J X b => h.1)) hQP

/-- The representative family discharges the coverage and disjointness inputs to the counting obstruction. -/
theorem representativeImage_no_injection (E : (α → Prop) → Prop) (B : β → Prop) (P : Prop)
    (rc : □ (Classicism.P.RigidComprehension (α → Prop))) (he : Rigid E)
    (ic : Classicism.P.IntensionalChoice ((α → Prop) → β → Prop))
    (separate : ∀ X Y, E X → E Y → X ≠ Y → EntailmentOrder P (¬ (X ≡ Y)))
    (obstruction : ∀ Q (D : (α → Prop) → β → Prop),
      (∀ X b, E X → B b → Below P (D X b)) →
      (∀ X Y b, E X → E Y → B b → X ≠ Y → □ (¬ (D X b ∧ D Y b))) →
      (∀ X, E X → EntailmentOrder Q (∃ b, B b ∧ D X b)) → Q = False) :
    EntailmentOrder P (¬ Embeds (RepresentativeImage E) B) := by
  apply local_injection_exclusion (RepresentativeImage E) B P ic
  intro Q hQP J hJ
  exact obstruction Q (RepresentativeValue Q J)
    (fun X b _ _ => representativeValue_below P Q J hQP X b)
    (fun X Y b hX hY _ hn => representativeValue_disjoint E B Q J X Y b hJ
      (entailment_trans Q P (¬ (X ≡ Y)) hQP (separate X Y hX hY hn)))
    (representativeValue_cover E B Q J rc he hJ)

#classicism_check rigid_representative_exists representativeValue_cover_current representativeValue_cover representativeValue_conflict representativeValue_disjoint representativeValue_below representativeImage_no_injection
#classicism_types rigid_representative_exists representativeValue_cover_current representativeValue_cover representativeValue_conflict representativeValue_disjoint representativeValue_below representativeImage_no_injection
end Classicism.MathematicalContingency
