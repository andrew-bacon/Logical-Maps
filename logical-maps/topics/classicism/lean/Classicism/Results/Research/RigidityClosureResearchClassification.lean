import Classicism.Results.Research.RigidityClosureResearchJoins

/-!
# The IC/RC/TR/WRP equivalence over ND and Boolean Completeness

Direct source: research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md,
§7, "Exact classification over ND + BC" (original research, unpaginated,
misc, 22 October 2026). The displayed arrows record the exact finite instances
used. In particular RC at the higher property type supplies WRP at the lower
relation type; no same-type converse is silently claimed.
-/
namespace Classicism.Research.RigidityClosure
open Classicism.P Classicism.Paper
variable {σ : Type} [Ty σ]

theorem nd_bc_ic_implies_rc : NecessityOfDistinctness Prop →
    BooleanCompleteness (σ → Prop) → InextensibleComprehension (σ → Prop) →
    RigidComprehension (σ → Prop) := fun nd bc ic =>
  Proofs.tame_rigidity_and_weak_rigid_comprehension_imply_rigid_comprehension
    (Classicism.Research.InextensiblePower.nd_ic_tame nd ic)
    (nd_bc_weak_comprehension (Proofs.nd_of_nd_t nd) bc)

theorem nd_bc_tame_implies_rc : NecessityOfDistinctness Prop →
    BooleanCompleteness (σ → Prop) → TameRigidity (σ → Prop) →
    RigidComprehension (σ → Prop) := fun nd bc tr =>
  Proofs.tame_rigidity_and_weak_rigid_comprehension_imply_rigid_comprehension tr
    (nd_bc_weak_comprehension (Proofs.nd_of_nd_t nd) bc)

theorem nd_bc_weak_power_implies_rc : NecessityOfDistinctness Prop →
    BooleanCompleteness (σ → Prop) → WeaklyRigidPower (σ → Prop) →
    RigidComprehension (σ → Prop) := fun nd bc wrp =>
  nd_bc_tame_implies_rc nd bc (Proofs.weakly_rigid_power_implies_tame_rigidity wrp)

theorem nd_higher_rc_implies_weak_power : NecessityOfDistinctness Prop →
    RigidComprehension ((σ → Prop) → Prop) → WeaklyRigidPower (σ → Prop) :=
  fun nd rc => Classicism.Research.InextensiblePower.nd_ic_weaklyRigidPower nd
    (Proofs.rigid_comprehension_r_implies_inextensible_comprehension_r rc)

theorem nd_bc_ic_iff_rc (nd : NecessityOfDistinctness Prop)
    (bc : BooleanCompleteness (σ → Prop)) :
    InextensibleComprehension (σ → Prop) ↔ RigidComprehension (σ → Prop) :=
  ⟨nd_bc_ic_implies_rc nd bc, Proofs.rigid_comprehension_r_implies_inextensible_comprehension_r⟩

theorem nd_bc_tame_iff_rc (nd : NecessityOfDistinctness Prop)
    (bc : BooleanCompleteness (σ → Prop)) :
    TameRigidity (σ → Prop) ↔ RigidComprehension (σ → Prop) :=
  ⟨nd_bc_tame_implies_rc nd bc, Proofs.rigid_comprehension_implies_tame_rigidity⟩

/-- Exact necessary all-type route from C5 to ambient complement closure. -/
theorem c5_implies_weak_complement : NecNecessityOfDistinctness Prop →
    WeakComplementClosure σ := fun c5 => weak_complement_iff_nd_barcan.2
      ⟨Proofs.nd_of_nd_t (box_elim c5), Proofs.bf_of_box_nd_t c5⟩

theorem c5_implies_rigid_complement : NecNecessityOfDistinctness Prop →
    RigidComplementClosure σ := fun c5 => rigid_complement_iff_nd_necessary_barcan.2
      ⟨Proofs.nd_of_nd_t (box_elim c5),
        Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r c5⟩

end Classicism.Research.RigidityClosure
