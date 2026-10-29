import Classicism.Results.NumericalRigidity.Inductive

/-! Goodsell, Arithmetic is Necessary (2024), Lemma 8, with countable
Boolean completeness in its LUB formulation. Countability is expressed by
a relation into the object-language carrier, not by external Lean naturals.
OpenAI Codex, prompted by Andrew Bacon, 28 October 2026. -/
namespace Classicism.Numerical
open Classicism.Paper

/-- The existing Ctbl definition, relative to an arbitrary number carrier. -/
def CountableOver {ν τ : Type} [Ty ν] [Ty τ] (N : ν → Prop) (A : τ → Prop) : Prop :=
  ∃ R : τ → ν → Prop, ∀ y z, A y ∧ A z →
    ((∃ n, N n ∧ R y n ∧ R z n) ↔ y = z)

/-- Every family countable over N has a least upper bound in the Boolean order. -/
def CountableBooleanCompleteOver {ν : Type} [Ty ν] (N : ν → Prop)
    (τ : Type) [Rel τ] : Prop :=
  ∀ F : τ → Prop, CountableOver N F → ∃ B : τ, LUB B F

def CountableBooleanCompleteAt (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  CountableBooleanCompleteOver (@FiniteCardinality σ _) τ

theorem countableOver_finiteCardinality_iff {σ τ : Type} [Ty σ] [Ty τ]
    (F : τ → Prop) : CountableOver (@FiniteCardinality σ _) F ↔ Ctbl σ F := Iff.rfl

/-- The singleton family is countable over its carrier, without Infinity. -/
theorem singletonFamily_countable {ν : Type} [Ty ν] (N : ν → Prop) :
    CountableOver N (SingletonFamily N) := by
  refine ⟨fun Y n => Y = (fun m => n = m), ?_⟩
  intro Y Z h
  constructor
  · intro he
    obtain ⟨n, _, hy, hz⟩ := he
    exact hy.trans hz.symm
  · intro he
    obtain ⟨n, hn, hy⟩ := h.1
    exact ⟨n, hn, hy, he.symm.trans hy⟩

theorem countableBooleanCompleteOver_of_booleanComplete {ν α : Type} [Ty ν] [Ty α]
    (N : ν → Prop) (bc : BooleanCompleteAt (α → Prop)) :
    CountableBooleanCompleteOver N (α → Prop) :=
  fun F _ => booleanCompleteAt_lub bc F

section generic
variable {ν : Type} [Rel ν] (z : ν) (s : ν → ν)

theorem inductiveClosure_restricted_barcan_of_countable
    (cbc : CountableBooleanCompleteOver (InductiveClosure z s) (ν → Prop))
    (X : ν → Prop) (hx : ∀ n, InductiveClosure z s n → □ (X n)) :
    □ (∀ n, InductiveClosure z s n → X n) := by
  obtain ⟨B, hb⟩ := cbc (SingletonFamily (InductiveClosure z s))
    (singletonFamily_countable (InductiveClosure z s))
  exact inductiveClosure_restricted_barcan_of_lub z s B hb X hx

theorem inductiveClosure_weaklyRigid_of_countable
    (cbc : CountableBooleanCompleteOver (InductiveClosure z s) (ν → Prop)) :
    WeaklyRigid (InductiveClosure z s) :=
  ⟨inductiveClosure_box z s, inductiveClosure_restricted_barcan_of_countable z s cbc⟩

theorem inductiveClosure_rigid_of_box_countable
    (cbc : □ (CountableBooleanCompleteOver (InductiveClosure z s) (ν → Prop))) :
    Rigid (InductiveClosure z s) :=
  (rigid_iff_box_weaklyRigid _).2
    (modal_K _ _ (nec% (inductiveClosure_weaklyRigid_of_countable z s)) cbc)
end generic

section specializations
variable {σ : Type} [Ty σ]

theorem finiteCardinality_weaklyRigid_of_countable
    (cbc : CountableBooleanCompleteAt σ (((σ → Prop) → Prop) → Prop)) :
    WeaklyRigid (@FiniteCardinality σ _) :=
  inductiveClosure_weaklyRigid_of_countable (ZeroCard σ) SucCard cbc

theorem finiteCardinality_rigid_of_box_countable
    (cbc : □ (CountableBooleanCompleteAt σ (((σ → Prop) → Prop) → Prop))) :
    Rigid (@FiniteCardinality σ _) :=
  inductiveClosure_rigid_of_box_countable (ZeroCard σ) SucCard cbc

end specializations

#classicism_check countableOver_finiteCardinality_iff singletonFamily_countable
  countableBooleanCompleteOver_of_booleanComplete inductiveClosure_restricted_barcan_of_countable
  inductiveClosure_weaklyRigid_of_countable inductiveClosure_rigid_of_box_countable
  finiteCardinality_weaklyRigid_of_countable finiteCardinality_rigid_of_box_countable
#classicism_types countableOver_finiteCardinality_iff singletonFamily_countable
  countableBooleanCompleteOver_of_booleanComplete inductiveClosure_restricted_barcan_of_countable
  inductiveClosure_weaklyRigid_of_countable inductiveClosure_rigid_of_box_countable
  finiteCardinality_weaklyRigid_of_countable finiteCardinality_rigid_of_box_countable
end Classicism.Numerical
