import Classicism.Results.MathematicalContingency.FiniteCardinalityRigidity

/-! The direct unboxed-RC route: an inductive closure is identical to any
rigid coextensive representative. No Boolean-completeness assumption is needed.
OpenAI Codex, prompted by Andrew Bacon, 28 October 2026. -/
namespace Classicism.MathematicalContingency
open Classicism.Paper
section generic
variable {ν : Type} [Rel ν] (z : ν) (s : ν → ν)

theorem inductiveClosure_le_rigid_coext (R : ν → Prop) (hr : Rigid R)
    (co : ∀ n, InductiveClosure z s n ↔ R n) : InductiveClosure z s ≤ R := by
  have hz : □ (R z) := box_elim hr.1 z ((co z).1 (inductiveClosure_zero z s))
  have hs : □ (∀ n, R n → R (s n)) :=
    box_elim hr.2 (fun n => R (s n)) (fun n hn =>
      box_elim hr.1 (s n) ((co (s n)).1 (inductiveClosure_suc z s n ((co n).2 hn))))
  exact (le_iff _ _).2 (modal_K _ _
    (modal_K _ _ (nec% (inductiveClosure_induction z s R)) hz) hs)

theorem rigid_coext_le_inductiveClosure (R : ν → Prop) (hr : Rigid R)
    (co : ∀ n, InductiveClosure z s n ↔ R n) : R ≤ InductiveClosure z s :=
  (le_iff _ _).2 (box_elim hr.2 (InductiveClosure z s)
    (fun n hn => inductiveClosure_box z s n ((co n).2 hn)))

theorem inductiveClosure_eq_rigid_coext (R : ν → Prop) (hr : Rigid R)
    (co : ∀ n, InductiveClosure z s n ↔ R n) : InductiveClosure z s = R :=
  le_antisymm_rel _ _ (inductiveClosure_le_rigid_coext z s R hr co)
    (rigid_coext_le_inductiveClosure z s R hr co)

theorem inductiveClosure_rigid_of_rc (rc : P.RigidComprehension (ν → Prop)) :
    Rigid (InductiveClosure z s) := by
  obtain ⟨R, hr, co⟩ := rc (InductiveClosure z s)
  exact (inductiveClosure_eq_rigid_coext z s R hr co).symm ▸ hr
end generic

theorem finiteCardinality_rigid_of_rc {σ : Type} [Ty σ]
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → Prop)) :
    Rigid (@FiniteCardinality σ _) := inductiveClosure_rigid_of_rc (ZeroCard σ) SucCard rc

theorem lowerNat_rigid_of_rc {σ : Type} [Ty σ]
    (rc : P.RigidComprehension (((σ → Prop) → Prop) → Prop)) :
    Rigid (@LowerNat σ _) := inductiveClosure_rigid_of_rc (AtLeastZero σ) SucCard rc

#classicism_check inductiveClosure_le_rigid_coext rigid_coext_le_inductiveClosure
  inductiveClosure_eq_rigid_coext inductiveClosure_rigid_of_rc
  finiteCardinality_rigid_of_rc lowerNat_rigid_of_rc
#classicism_types inductiveClosure_le_rigid_coext rigid_coext_le_inductiveClosure
  inductiveClosure_eq_rigid_coext inductiveClosure_rigid_of_rc
  finiteCardinality_rigid_of_rc lowerNat_rigid_of_rc
end Classicism.MathematicalContingency
