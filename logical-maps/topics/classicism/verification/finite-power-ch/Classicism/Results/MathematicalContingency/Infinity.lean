import Classicism.Principles.Infinity

/-! Reconstructed by OpenAI Codex, prompted by Andrew Bacon, 25 October 2026.
The comparison with the repository's exact-count infinity is a statement, not an axiom. -/
namespace Classicism.MathematicalContingency
def AtLeastZero (σ : Type) [Ty σ] : (σ → Prop) → Prop := fun _ => True
def LowerNat {σ : Type} [Ty σ] (n : (σ → Prop) → Prop) : Prop :=
  ∀ Z : ((σ → Prop) → Prop) → Prop, (Z (AtLeastZero σ) ∧ ∀ m, Z m → Z (SucCard m)) → Z n
def LowerPeano (σ : Type) [Ty σ] : Prop :=
  (∀ n, LowerNat n → AtLeastZero σ ≠ SucCard n) ∧
  (∀ m n : (σ → Prop) → Prop, LowerNat m → LowerNat n → SucCard m = SucCard n → m = n)
def DraftBoxInfinity (σ : Type) [Ty σ] : Prop := □ (LowerPeano σ)
def RepositoryBoxInfinity (σ : Type) [Ty σ] : Prop := □ (P.AxiomOfInfinity σ)
def InfinityComparison (σ : Type) [Ty σ] : Prop :=
  RepositoryBoxInfinity σ ↔ DraftBoxInfinity σ
end Classicism.MathematicalContingency
