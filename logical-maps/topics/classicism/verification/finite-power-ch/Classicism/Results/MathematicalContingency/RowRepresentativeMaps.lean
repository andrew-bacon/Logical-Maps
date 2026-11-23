import Classicism.Results.MathematicalContingency.CountableRowCoverage
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α τ : Type} [Ty α] [Ty τ]

def RowRepresentatives (A : α → Prop) (I : τ → Prop) (M : τ → (α → Prop) → Prop)
    (a : τ) (U : α → Prop) : Prop := I a ∧ RigidPower A U ∧ ∃ X, M a X ∧ X ≡ U

theorem rowRepresentatives_maps (A : α → Prop) (I : τ → Prop) (E : (α → Prop) → Prop)
    (M : τ → (α → Prop) → Prop) (rc : Classicism.P.RigidComprehension (α → Prop))
    (maps : Maps M I E) (sub : ∀ X, E X → ∀ n, X n → A n) :
    Maps (RowRepresentatives A I M) I (RigidPower A) := by
  refine ⟨fun a U h => ⟨h.1,h.2.1⟩,?_,?_⟩
  · intro a ha
    obtain ⟨X,hX,hM⟩ := maps.2.1 a ha
    obtain ⟨U,hU,co⟩ := rc X
    have hu : RigidPower A U := ⟨hU,fun n hn => sub X hX n ((co n).mpr hn)⟩
    exact ⟨U,hu,ha,hu,X,hM,co⟩
  · intro a U V hu hv
    obtain ⟨X,hX,coU⟩ := hu.2.2
    obtain ⟨Y,hY,coV⟩ := hv.2.2
    have e := maps.2.2 a X Y hX hY
    subst Y
    exact rigid_eq_of_coext U V hu.2.1.1 hv.2.1.1 (fun n => (coU n).symm.trans (coV n))

theorem rowRepresentatives_necessary_maps (A : α → Prop) (I : τ → Prop) (E : (α → Prop) → Prop)
    (M : τ → (α → Prop) → Prop) (rc : □ (Classicism.P.RigidComprehension (α → Prop)))
    (maps : □ (Maps M I E)) (sub : □ (∀ X, E X → ∀ n, X n → A n)) :
    □ (Maps (RowRepresentatives A I M) I (RigidPower A)) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _ (nec% (rowRepresentatives_maps A I E M)) rc) maps) sub

theorem rowRepresentatives_surjects (A : α → Prop) (I : τ → Prop) (M : τ → (α → Prop) → Prop)
    (maps : Maps (RowRepresentatives A I M) I (RigidPower A))
    (cover : ∀ S, RigidPower A S → RowCovered I M S) :
    Surjects (RowRepresentatives A I M) I (RigidPower A) := by
  refine ⟨maps,?_⟩
  intro S hs
  obtain ⟨a,X,ha,hX,co⟩ := cover S hs
  exact ⟨a,ha,ha,hs,X,hX,co⟩

#classicism_check rowRepresentatives_maps rowRepresentatives_necessary_maps rowRepresentatives_surjects
#classicism_types rowRepresentatives_maps rowRepresentatives_necessary_maps rowRepresentatives_surjects
end Classicism.MathematicalContingency
