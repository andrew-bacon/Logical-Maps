import Classicism.Results.MathematicalContingency.CountableRowNames
import Classicism.Results.MathematicalContingency.StableMaps
namespace Classicism.MathematicalContingency
variable {α τ : Type} [Ty α] [Ty τ]

theorem indexedNames_frozen_map (A : α → Prop) (I : τ → Prop)
    (T : τ → α → Prop → Prop) (hI : Rigid I) (ndI : DomainND I)
    (names : Maps (IndexedName A I T) I (NameCarrier A I T))
    (rcE : P.RigidComprehension ((α → Prop) → Prop))
    (rcM : P.RigidComprehension (τ → (α → Prop) → Prop)) :
    ∃ E M, Rigid E ∧ Rigid M ∧ (∀ X, E X ↔ NameCarrier A I T X) ∧
      (∀ a X, M a X ↔ IndexedName A I T a X) ∧ □ (Maps M I E) ∧
      □ (∀ X, E X → ∀ n, X n → A n) := by
  obtain ⟨E,hE,eE⟩ := rcE (NameCarrier A I T)
  obtain ⟨M,hM,eM⟩ := rcM (IndexedName A I T)
  have hm : Maps M I E := by
    refine ⟨?_,?_,?_⟩
    · intro a X h
      have hn := names.1 a X ((eM a X).mpr h)
      exact ⟨hn.1,(eE X).mp hn.2⟩
    · intro a ha
      obtain ⟨X,hX,h⟩ := names.2.1 a ha
      exact ⟨X,(eE X).mp hX,(eM a X).mp h⟩
    · intro a X Y hX hY
      exact names.2.2 a X Y ((eM a X).mpr hX) ((eM a Y).mpr hY)
  exact ⟨E,M,hE,hM,fun X => (eE X).symm,fun a X => (eM a X).symm,
    rigid_maps_necessary I E M hI hE hM ndI hm,
    restricted_barcan_unary E (fun X => ∀ n, X n → A n) hE
      (fun X hX => nameCarrier_subsets A I T X ((eE X).mpr hX))⟩

#classicism_check indexedNames_frozen_map
#classicism_types indexedNames_frozen_map
end Classicism.MathematicalContingency
