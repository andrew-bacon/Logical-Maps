import Classicism.Models.OldNewPairs

/-!
# Unboxed necessity of distinctness at the old/new root

Source: writeups/symmetric-old-new-individuals.md, ND at every type at E;
research/2026-10-22/notes/old-new-boolean-completeness-and-rigidity-separation.md.
Original Lean proof (misc), 22 October 2026. Finite invertibility is proved
for the actual arrow classes in OldNewBase, not postulated here.
-/

namespace Classicism.Meta.Intensional.OldNew

open CategoryTheory
noncomputable section

theorem root_transport_injective (σ : Ty) {V : cat.Ob} (f : E ⟶ V) :
    Function.Injective ((model.inner σ).map f) := by
  cases σ with
  | e => exact f.2.1
  | var _ => exact f.2.1
  | rel ρ =>
    intro F G he
    apply model.Incl_injective (.rel ρ) E
    obtain ⟨SF, hSF, hpF⟩ := SymBase.finPinned (S := base) (.rel ρ) F
    obtain ⟨SG, hSG, hpG⟩ := SymBase.finPinned (S := base) (.rel ρ) G
    ext ⟨U, a, h⟩
    obtain ⟨k, hk⟩ := finite_inverse f h (hSF.union hSG)
    have eF := profile_agree hpF (fun x hx => hk x (Or.inl hx)) a
    have eG := profile_agree hpG (fun x hx => hk x (Or.inr hx)) a
    have hem := congrArg (model.incl ρ V) he
    rw [model.incl_map, model.incl_map] at hem
    have hm : profile F (f ≫ k) a ↔ profile G (f ≫ k) a :=
      Iff.of_eq (congrArg (fun R : Intension model.inner ρ V =>
        (⟨U, a, k⟩ : Tuple model.inner ρ V) ∈ R) hem)
    exact eF.symm.trans (hm.trans eG)

theorem root_nd (σ : Ty) : model.HoldsSentence (P.NecessityOfDistinctness.quoted σ) := by
  change model.Holds (𝟙 E) (Sentence.nd σ) .nil
  exact (model.holds_nd_iff isModel σ (𝟙 E)).2 (root_transport_injective σ)

end
end Classicism.Meta.Intensional.OldNew
