import Classicism.Results.Research.RigidityClosureResearchClassificationCertificates

/-!
# Full-schema IC / RC / TR / WRP equivalence over ND and BC

This is an assembly of translated C derivations, not an object-level
quantification over types. Every relational type is its finite argument list
followed by t, including t itself. No same-type shortcut for WRP is used.
-/
namespace Classicism.Meta.Research.RigidityClosure
open AxiomSet

private theorem schema_subset_args (q : RTy → Sentence Signature.pure) :
    (fun a => ∃ ρ : RTy, ρ.Closed ∧ a = q ρ) ⊆
      (fun a => ∃ σs : List Ty, Ty.AllClosed σs ∧ a = q (σs ⇒* .t)) :=
  fun _ ⟨ρ, hρ, h⟩ =>
    ⟨ρ.args, RTy.closed_args hρ, h.trans (congrArg q (RTy.ofArgs_args ρ).symm)⟩

abbrev Background := P.NecessityOfDistinctness.schema ∪ P.BooleanCompleteness.schema

theorem ic_implies_rc : Background ∪ P.InextensibleComprehension.schema ⟹
    P.RigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Classicism.Research.RigidityClosure.nd_bc_ic_implies_rc.listEntails

theorem tame_implies_rc : Background ∪ P.TameRigidity.schema ⟹
    P.RigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Classicism.Research.RigidityClosure.nd_bc_tame_implies_rc.listEntails

theorem weak_power_implies_rc : Background ∪ P.WeaklyRigidPower.schema ⟹
    P.RigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Classicism.Research.RigidityClosure.nd_bc_weak_power_implies_rc.listEntails

theorem rc_implies_ic : Background ∪ P.RigidComprehension.schema ⟹
    P.InextensibleComprehension.schema :=
  Entails.trans (Entails.union_right Background P.RigidComprehension.schema)
    Classicism.Proofs.rigid_comprehension_r_implies_inextensible_comprehension_r.entails

theorem rc_implies_tame : Background ∪ P.RigidComprehension.schema ⟹
    P.TameRigidity.schema :=
  Entails.trans (Entails.union_right Background P.RigidComprehension.schema)
    Classicism.Proofs.rigid_comprehension_implies_tame_rigidity.entails

theorem rc_implies_weak_power : Background ∪ P.RigidComprehension.schema ⟹
    P.WeaklyRigidPower.schema :=
  have nd := Entails.trans (Entails.union_left Background P.RigidComprehension.schema)
    (Entails.union_left P.NecessityOfDistinctness.schema P.BooleanCompleteness.schema)
  have rc := Entails.union_right Background P.RigidComprehension.schema
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union nd rc)
      Classicism.Research.RigidityClosure.nd_higher_rc_implies_weak_power.listEntails)

/-- Mutual full-schema entailment of IC and RC over the exact unboxed base. -/
theorem ic_rc_equivalent :
    ((Background ∪ P.InextensibleComprehension.schema) ⟹
      (Background ∪ P.RigidComprehension.schema)) ∧
    ((Background ∪ P.RigidComprehension.schema) ⟹
      (Background ∪ P.InextensibleComprehension.schema)) :=
  ⟨Entails.union (Entails.union_left _ _) ic_implies_rc,
   Entails.union (Entails.union_left _ _) rc_implies_ic⟩

/-- Mutual full-schema entailment of TR and RC over the exact unboxed base. -/
theorem tame_rc_equivalent :
    ((Background ∪ P.TameRigidity.schema) ⟹ (Background ∪ P.RigidComprehension.schema)) ∧
    ((Background ∪ P.RigidComprehension.schema) ⟹ (Background ∪ P.TameRigidity.schema)) :=
  ⟨Entails.union (Entails.union_left _ _) tame_implies_rc,
   Entails.union (Entails.union_left _ _) rc_implies_tame⟩

/-- WRP is equivalent to the other three schemata, despite its higher-type premise. -/
theorem weak_power_rc_equivalent :
    ((Background ∪ P.WeaklyRigidPower.schema) ⟹ (Background ∪ P.RigidComprehension.schema)) ∧
    ((Background ∪ P.RigidComprehension.schema) ⟹ (Background ∪ P.WeaklyRigidPower.schema)) :=
  ⟨Entails.union (Entails.union_left _ _) weak_power_implies_rc,
   Entails.union (Entails.union_left _ _) rc_implies_weak_power⟩

end Classicism.Meta.Research.RigidityClosure

#print axioms Classicism.Meta.Research.RigidityClosure.ic_rc_equivalent
#print axioms Classicism.Meta.Research.RigidityClosure.tame_rc_equivalent
#print axioms Classicism.Meta.Research.RigidityClosure.weak_power_rc_equivalent
