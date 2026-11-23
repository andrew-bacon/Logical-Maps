import Classicism.Results.MathematicalContingency.RepresentedPower

/-! RC constructs a represented power using the existing rigid-power carrier.
OpenAI Codex, prompted by Andrew Bacon, 31 October 2026.
The definition of Pow itself has no RC assumption and includes every subset.
-/
namespace Classicism.MathematicalContingency.FinitePower
variable {α : Type} [Ty α]

theorem rigidPower_represents (A : α → Prop)
    (rc : P.RigidComprehension (α → Prop)) :
    RepresentsPower (fun X a => RigidPower A X ∧ X a) (RigidPower A) A := by
  refine ⟨fun _ a h => ⟨h.1,h.1.2 a h.2⟩,?_,?_⟩
  · intro X Y hx hy e
    exact rigid_eq_of_coext X Y hx.1 hy.1
      (fun a => ⟨fun h => ((e a).mp ⟨hx,h⟩).2,fun h => ((e a).mpr ⟨hy,h⟩).2⟩)
  · intro Z sub
    obtain ⟨X,hx,e⟩ := rc Z
    have hX : RigidPower A X := ⟨hx,fun a h => sub a ((e a).mpr h)⟩
    exact ⟨X,hX,fun a => ⟨fun h => (e a).mpr h.2,fun h => ⟨hX,(e a).mp h⟩⟩⟩

theorem pow_rigidPower (A : α → Prop) (rc : P.RigidComprehension (α → Prop)) :
    Pow (RigidPower A) A := ⟨_,rigidPower_represents A rc⟩

#classicism_check rigidPower_represents pow_rigidPower
#classicism_types rigidPower_represents pow_rigidPower
end Classicism.MathematicalContingency.FinitePower
