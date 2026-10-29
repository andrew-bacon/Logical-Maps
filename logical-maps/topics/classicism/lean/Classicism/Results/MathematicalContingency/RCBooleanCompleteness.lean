import Classicism.Results.MathematicalContingency.CountableRigidity

/-! RC supplies meets by rigidifying the family to be intersected.
All RC assumptions, including their exact types and boxes, remain explicit.
OpenAI Codex, prompted by Andrew Bacon, 28 October 2026. -/
namespace Classicism.MathematicalContingency
open Classicism.Paper
variable {α : Type} [Ty α]

def RigidFamilyMeet (A : (α → Prop) → Prop) : α → Prop :=
  fun x => ∀ Y, A Y → Y x

theorem rigidFamilyMeet_lower (F A : (α → Prop) → Prop)
    (ha : Rigid A) (co : ∀ Y, F Y ↔ A Y) : LB (RigidFamilyMeet A) F := by
  intro Y hy
  exact (le_iff _ _).2 (modal_K _ _
    (nec% (fun (hy : A Y) (x : α) (hx : RigidFamilyMeet A x) => hx Y hy))
    (box_elim ha.1 Y ((co Y).1 hy)))

theorem rigidFamilyMeet_greatest (F A : (α → Prop) → Prop)
    (ha : Rigid A) (co : ∀ Y, F Y ↔ A Y) (Z : α → Prop)
    (hz : LB Z F) : Z ≤ RigidFamilyMeet A := by
  have h : □ (∀ Y, A Y → ∀ x, Z x → Y x) :=
    box_elim ha.2 (fun Y => ∀ x, Z x → Y x)
      (fun Y hy => (le_iff _ _).1 (hz Y ((co Y).2 hy)))
  exact (le_iff _ _).2 (modal_K _ _
    (nec% (fun (h : ∀ Y, A Y → ∀ x, Z x → Y x) (x : α) (hx : Z x)
      (Y : α → Prop) (hy : A Y) => h Y hy x hx)) h)

theorem rigidFamilyMeet_glb (F A : (α → Prop) → Prop)
    (ha : Rigid A) (co : ∀ Y, F Y ↔ A Y) : GLB (RigidFamilyMeet A) F :=
  fun Z => ⟨rigidFamilyMeet_greatest F A ha co Z,
    fun hz Y hy => le_trans_rel Z (RigidFamilyMeet A) Y hz
      (rigidFamilyMeet_lower F A ha co Y hy)⟩

theorem booleanCompleteAt_of_rc
    (rc : P.RigidComprehension ((α → Prop) → Prop)) : BooleanCompleteAt (α → Prop) := by
  intro F
  obtain ⟨A, ha, co⟩ := rc F
  exact ⟨RigidFamilyMeet A, rigidFamilyMeet_glb F A ha co⟩

theorem box_booleanCompleteAt_of_box_rc
    (rc : □ (P.RigidComprehension ((α → Prop) → Prop))) :
    □ (BooleanCompleteAt (α → Prop)) :=
  modal_K _ _ (nec% (booleanCompleteAt_of_rc (α := α))) rc

theorem countableBooleanCompleteOver_of_rc {ν : Type} [Ty ν] (N : ν → Prop)
    (rc : P.RigidComprehension ((α → Prop) → Prop)) :
    CountableBooleanCompleteOver N (α → Prop) :=
  countableBooleanCompleteOver_of_booleanComplete N (booleanCompleteAt_of_rc rc)

theorem box_countableBooleanCompleteOver_of_box_rc {ν : Type} [Ty ν] (N : ν → Prop)
    (rc : □ (P.RigidComprehension ((α → Prop) → Prop))) :
    □ (CountableBooleanCompleteOver N (α → Prop)) :=
  modal_K _ _ (nec% (countableBooleanCompleteOver_of_rc N)) rc

/-- Explicit composition through Goodsell's countable-completeness result. -/
theorem lowerNat_rigid_of_box_rc_family {σ : Type} [Ty σ]
    (rc : □ (P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))) :
    Rigid (@LowerNat σ _) :=
  lowerNat_rigid_of_box_countable (box_countableBooleanCompleteOver_of_box_rc LowerNat rc)

theorem finiteCardinality_rigid_of_box_rc_family {σ : Type} [Ty σ]
    (rc : □ (P.RigidComprehension ((((σ → Prop) → Prop) → Prop) → Prop))) :
    Rigid (@FiniteCardinality σ _) :=
  finiteCardinality_rigid_of_box_countable
    (box_countableBooleanCompleteOver_of_box_rc FiniteCardinality rc)

#classicism_check rigidFamilyMeet_lower rigidFamilyMeet_greatest rigidFamilyMeet_glb
  booleanCompleteAt_of_rc box_booleanCompleteAt_of_box_rc countableBooleanCompleteOver_of_rc
  box_countableBooleanCompleteOver_of_box_rc lowerNat_rigid_of_box_rc_family
  finiteCardinality_rigid_of_box_rc_family
#classicism_types rigidFamilyMeet_lower rigidFamilyMeet_greatest rigidFamilyMeet_glb
  booleanCompleteAt_of_rc box_booleanCompleteAt_of_box_rc countableBooleanCompleteOver_of_rc
  box_countableBooleanCompleteOver_of_box_rc lowerNat_rigid_of_box_rc_family
  finiteCardinality_rigid_of_box_rc_family
end Classicism.MathematicalContingency
