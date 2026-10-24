import Classicism.Results.Research.RigidityClosureResearchClassification

/-! Exact iff statements packaged for finite-tuple certificates, including t.
The mathematical proofs are in the frozen join and finite-closure modules. -/
namespace Classicism.Research.RigidityClosure
open Classicism.P Classicism.Paper

def NecessarySingletonJoinCharacterization (σ : Type) [Ty σ] : Prop :=
  ∀ F : σ → Prop, Rigid F ↔ □ (LUB F (SingletonFamily F))
def WeakComplementCharacterization (σ : Type) [Ty σ] : Prop :=
  WeakComplementClosure σ ↔ (NecessityOfDistinctness σ ∧ Barcan σ)
def RigidComplementCharacterization (σ : Type) [Ty σ] : Prop :=
  RigidComplementClosure σ ↔ (NecessityOfDistinctness σ ∧ NecBarcan σ)

theorem necessary_singleton_join_characterization {σ : Type} [Ty σ] :
    NecessarySingletonJoinCharacterization σ := rigid_iff_necessary_singleton_join

theorem weak_complement_characterization {σ : Type} [Ty σ] :
    WeakComplementCharacterization σ := weak_complement_iff_nd_barcan

theorem rigid_complement_characterization {σ : Type} [Ty σ] :
    RigidComplementCharacterization σ := rigid_complement_iff_nd_necessary_barcan

end Classicism.Research.RigidityClosure
