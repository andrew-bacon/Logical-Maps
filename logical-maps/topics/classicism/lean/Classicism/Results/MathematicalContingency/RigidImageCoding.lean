import Classicism.Results.MathematicalContingency.CarrierTheory

/-!
Rigid codes for predicate images under a relational injection.
OpenAI Codex, prompted by Andrew Bacon, 26 October 2026.
Only current RC at the target predicate type is used; no representative
function, source RC, carrier rigidity or necessary functionality is assumed.
-/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α β γ : Type} [Ty α] [Ty β] [Ty γ]

def PredicateImage (F : α → β → Prop) (X : α → Prop) (y : β) : Prop :=
  ∃ x, X x ∧ F x y

def RigidImageCode (B : β → Prop) (F : α → β → Prop)
    (X : α → Prop) (Y : β → Prop) : Prop :=
  RigidPower B Y ∧ ∀ y, PredicateImage F X y ↔ Y y

theorem predicateImage_sub (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (maps : Maps F A B) (X : α → Prop) : ∀ y, PredicateImage F X y → B y := by
  intro y h
  obtain ⟨x,_,hxy⟩ := h
  exact (maps.1 x y hxy).2

theorem predicateImage_reflect (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (injects : Injects F A B) (X Z : α → Prop) (sub : ∀ x, X x → A x)
    (images : ∀ y, PredicateImage F X y → PredicateImage F Z y) : ∀ x, X x → Z x := by
  intro x hx
  obtain ⟨y,_,hxy⟩ := injects.1.2.1 x (sub x hx)
  obtain ⟨z,hz,hzy⟩ := images y ⟨x,hx,hxy⟩
  exact (injects.2 z x y hzy hxy) ▸ hz

theorem rigidImageCode_exists (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (maps : Maps F A B) (rc : P.RigidComprehension (β → Prop)) (X : α → Prop) :
    ∃ Y, RigidImageCode B F X Y := by
  obtain ⟨Y,rigid,coext⟩ := rc (PredicateImage F X)
  exact ⟨Y,⟨rigid,fun y hy => predicateImage_sub A B F maps X y ((coext y).mpr hy)⟩,coext⟩

theorem rigidImageCode_functional (B : β → Prop) (F : α → β → Prop)
    (X : α → Prop) (Y Z : β → Prop)
    (hy : RigidImageCode B F X Y) (hz : RigidImageCode B F X Z) : Y = Z :=
  rigid_eq_of_coext Y Z hy.1.1 hz.1.1 (fun y => (hy.2 y).symm.trans (hz.2 y))

theorem rigidImageCode_reflect (A : α → Prop) (B : β → Prop) (F : α → β → Prop)
    (injects : Injects F A B) (X Z : α → Prop)
    (subX : ∀ x, X x → A x) (subZ : ∀ x, Z x → A x) (Y : β → Prop)
    (hx : RigidImageCode B F X Y) (hz : RigidImageCode B F Z Y) : X ≡ Z :=
  fun x => ⟨predicateImage_reflect A B F injects X Z subX
    (fun y h => (hz.2 y).mpr ((hx.2 y).mp h)) x,
    predicateImage_reflect A B F injects Z X subZ
    (fun y h => (hx.2 y).mpr ((hz.2 y).mp h)) x⟩

/-- Any family separated by its current predicate extensions can be coded in
the rigid power of a carrier that bounds its predicate domain. -/
theorem rigidImageCode_embeds (A : α → Prop) (B : β → Prop) (H : γ → Prop)
    (T : γ → α → Prop) (rc : P.RigidComprehension (β → Prop)) (bound : Embeds A B)
    (sub : ∀ h, H h → ∀ x, T h x → A x)
    (separate : ∀ h k, H h → H k → (T h ≡ T k) → h = k) :
    Embeds H (RigidPower B) := by
  obtain ⟨F,hF⟩ := bound
  refine ⟨fun h Y => H h ∧ RigidImageCode B F (T h) Y,⟨⟨?_,?_,?_⟩,?_⟩⟩
  · intro h Y hy
    exact ⟨hy.1,hy.2.1⟩
  · intro h hh
    obtain ⟨Y,hY⟩ := rigidImageCode_exists A B F hF.1 rc (T h)
    exact ⟨Y,hY.1,hh,hY⟩
  · intro h Y Z hy hz
    exact rigidImageCode_functional B F (T h) Y Z hy.2 hz.2
  · intro h k Y hh hk
    exact separate h k hh.1 hk.1
      (rigidImageCode_reflect A B F hF (T h) (T k) (sub h hh.1) (sub k hk.1) Y hh.2 hk.2)

theorem rigidPower_embeds_of_embeds (A : α → Prop) (B : β → Prop)
    (rc : P.RigidComprehension (β → Prop)) (bound : Embeds A B) :
    Embeds (RigidPower A) (RigidPower B) :=
  rigidImageCode_embeds A B (RigidPower A) (fun X x => X x) rc bound
    (fun _ h => h.2) (fun X Z hx hz coext => rigid_eq_of_coext X Z hx.1 hz.1 coext)

#classicism_check predicateImage_sub predicateImage_reflect rigidImageCode_exists
  rigidImageCode_functional rigidImageCode_reflect rigidImageCode_embeds rigidPower_embeds_of_embeds
#classicism_types predicateImage_sub predicateImage_reflect rigidImageCode_exists
  rigidImageCode_functional rigidImageCode_reflect rigidImageCode_embeds rigidPower_embeds_of_embeds
end Classicism.MathematicalContingency
