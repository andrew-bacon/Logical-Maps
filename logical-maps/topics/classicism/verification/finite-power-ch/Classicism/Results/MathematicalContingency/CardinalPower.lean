import Classicism.Results.MathematicalContingency.CarrierTheory
namespace Classicism.MathematicalContingency
variable {σ : Type} [Ty σ]
theorem embeds_rigidPower (rc : P.RigidComprehension (σ → Prop)) (A : σ → Prop) :
    Embeds A (RigidPower A) := by
  let F : σ → (σ → Prop) → Prop := fun a X => A a ∧ Rigid X ∧ ∀ x, X x ↔ (A x ∧ x = a)
  refine ⟨F,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro a X h; exact ⟨h.1,h.2.1,fun x hx => ((h.2.2 x).mp hx).1⟩
  · intro a ha
    obtain ⟨X,hX,hco⟩ := rc (fun x => A x ∧ x = a)
    exact ⟨X,⟨hX,fun x hx => ((hco x).mpr hx).1⟩,ha,hX,fun x => (hco x).symm⟩
  · intro a X Y hx hy
    exact rigid_eq_of_coext X Y hx.2.1 hy.2.1 (fun x => (hx.2.2 x).trans (hy.2.2 x).symm)
  · intro a b X ha hb
    exact ((hb.2.2 a).mp ((ha.2.2 a).mpr ⟨ha.1,rfl⟩)).2

theorem rigidPower_not_embeds (rc : P.RigidComprehension (σ → Prop)) (A : σ → Prop) :
    ¬ Embeds (RigidPower A) A := by
  intro h
  obtain ⟨F,hf⟩ := h
  obtain ⟨D,hd,hco⟩ := rc (fun a => A a ∧ ∀ X, F X a → ¬ X a)
  have hD : RigidPower A D := ⟨hd,fun a ha => ((hco a).mpr ha).1⟩
  obtain ⟨a,ha,hda⟩ := hf.1.2.1 D hD
  have hn : ¬ D a := fun h => ((hco a).mpr h).2 D hda h
  apply hn
  apply (hco a).mp
  refine ⟨ha,?_⟩
  intro X hxa hx
  have he : X = D := hf.2 X D a hxa hda
  exact hn (Eq.mp (congrArg (fun Z : σ → Prop => Z a) he) hx)

theorem cantor_rigidPower (rc : P.RigidComprehension (σ → Prop)) (A : σ → Prop) :
    Smaller A (RigidPower A) := ⟨embeds_rigidPower rc A,rigidPower_not_embeds rc A⟩
#classicism_check embeds_rigidPower rigidPower_not_embeds cantor_rigidPower
#classicism_types embeds_rigidPower rigidPower_not_embeds cantor_rigidPower
end Classicism.MathematicalContingency
