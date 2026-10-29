import Classicism.Results.NumericalRigidity.Countable
import Classicism.Results.NumericalRigidity.RigidComprehension
import Classicism.Principles.NumericalRigidity

namespace Classicism.Numerical

/-- The converse restricted-Barcan direction uses persistence alone. -/
theorem inductiveClosure_converse_barcan {ν : Type} [Rel ν] (z : ν) (s : ν → ν)
    (X : ν → Prop) (h : □ (∀ n, InductiveClosure z s n → X n)) :
    ∀ n, InductiveClosure z s n → □ (X n) :=
  fun n hn => modal_K _ _ (converse_barcan _ h n) (inductiveClosure_box z s n hn)

theorem numericalRigidity_iff_weaklyRigid {σ : Type} [Ty σ] :
    P.NumericalRigidity σ ↔ WeaklyRigid (@FiniteCardinality σ _) :=
  ⟨fun h => ⟨inductiveClosure_box (ZeroCard σ) SucCard, fun X hx => (h X).1 hx⟩,
    fun h X => ⟨h.2 X, inductiveClosure_converse_barcan (ZeroCard σ) SucCard X⟩⟩

theorem necNumericalRigidity_iff_rigid {σ : Type} [Ty σ] :
    P.NecNumericalRigidity σ ↔ Rigid (@FiniteCardinality σ _) := by
  constructor
  · intro h
    exact (rigid_iff_box_weaklyRigid _).2 (modal_K _ _
      (nec% (numericalRigidity_iff_weaklyRigid (σ := σ)).1) h)
  · intro h
    exact modal_K _ _ (nec% (numericalRigidity_iff_weaklyRigid (σ := σ)).2)
      ((rigid_iff_box_weaklyRigid _).1 h)

/-- Goodsell 2024, Lemmas 3 and 8; σ is any admitted type, including e. -/
theorem countable_boolean_completeness_implies_numerical_rigidity {σ : Type} [Ty σ]
    (h : P.CountableBooleanCompleteness σ (((σ → Prop) → Prop) → Prop)) :
    P.NumericalRigidity σ :=
  numericalRigidity_iff_weaklyRigid.2 (finiteCardinality_weaklyRigid_of_countable h)

theorem boolean_completeness_implies_numerical_rigidity {σ : Type} [Ty σ]
    (h : P.BooleanCompleteness (((σ → Prop) → Prop) → Prop)) :
    P.NumericalRigidity σ :=
  numericalRigidity_iff_weaklyRigid.2 (inductiveClosure_weaklyRigid (ZeroCard σ) SucCard h)

theorem necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity
    {σ : Type} [Ty σ]
    (h : P.NecCountableBooleanCompleteness σ (((σ → Prop) → Prop) → Prop)) :
    P.NecNumericalRigidity σ :=
  modal_K _ _ (nec% (countable_boolean_completeness_implies_numerical_rigidity (σ := σ))) h

theorem necessary_boolean_completeness_implies_necessary_numerical_rigidity
    {σ : Type} [Ty σ]
    (h : P.NecBooleanCompleteness (((σ → Prop) → Prop) → Prop)) :
    P.NecNumericalRigidity σ :=
  modal_K _ _ (nec% (boolean_completeness_implies_numerical_rigidity (σ := σ))) h

/-- Unboxed RC suffices even for the strong form. -/
theorem rigid_comprehension_implies_necessary_numerical_rigidity {σ : Type} [Ty σ]
    (h : P.RigidComprehension (((σ → Prop) → Prop) → Prop)) :
    P.NecNumericalRigidity σ :=
  necNumericalRigidity_iff_rigid.2 (finiteCardinality_rigid_of_rc h)

theorem necessary_numerical_rigidity_implies_numerical_rigidity {σ : Type} [Ty σ]
    (h : P.NecNumericalRigidity σ) : P.NumericalRigidity σ := box_elim h

/-- Usual Church numerals acting on a relational carrier, in the admitted type system. -/
def ChurchNumber (α : Type) [Rel α] : ((α → α) → α → α) → Prop :=
  InductiveClosure (fun _ x => x) (fun n f x => f (n f x))

theorem churchNumber_weaklyRigid {α : Type} [Rel α]
    (h : P.BooleanCompleteness (((α → α) → α → α) → Prop)) :
    WeaklyRigid (ChurchNumber α) :=
  inductiveClosure_weaklyRigid (ν := (α → α) → α → α) (fun _ x => x) (fun n f x => f (n f x)) h

theorem churchNumber_rigid {α : Type} [Rel α]
    (h : P.NecBooleanCompleteness (((α → α) → α → α) → Prop)) :
    Rigid (ChurchNumber α) :=
  inductiveClosure_rigid (ν := (α → α) → α → α) (fun _ x => x) (fun n f x => f (n f x)) h

#classicism_check inductiveClosure_converse_barcan numericalRigidity_iff_weaklyRigid necNumericalRigidity_iff_rigid countable_boolean_completeness_implies_numerical_rigidity boolean_completeness_implies_numerical_rigidity necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity necessary_boolean_completeness_implies_necessary_numerical_rigidity rigid_comprehension_implies_necessary_numerical_rigidity necessary_numerical_rigidity_implies_numerical_rigidity churchNumber_weaklyRigid churchNumber_rigid
#classicism_types inductiveClosure_converse_barcan numericalRigidity_iff_weaklyRigid necNumericalRigidity_iff_rigid countable_boolean_completeness_implies_numerical_rigidity boolean_completeness_implies_numerical_rigidity necessary_countable_boolean_completeness_implies_necessary_numerical_rigidity necessary_boolean_completeness_implies_necessary_numerical_rigidity rigid_comprehension_implies_necessary_numerical_rigidity necessary_numerical_rigidity_implies_numerical_rigidity churchNumber_weaklyRigid churchNumber_rigid
end Classicism.Numerical
