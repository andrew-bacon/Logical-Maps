import Classicism.Principles.Lattice

/-! Numerical Rigidity in the restricted-Barcan sense of Bacon and Zeng,
*A Theory of Necessities*, adapted to finite cardinality quantifiers.
The boxed form is the map's strong `Rigid` convention.
Formalization: OpenAI Codex (GPT-6), prompted by Andrew Bacon, 29 October 2026. -/
namespace Classicism.P

def NumericalRigidity (σ : Type) [Ty σ] : Prop :=
  ∀ X : ((σ → Prop) → Prop) → Prop,
    (∀ n, FiniteCardinality n → □ (X n)) ↔ □ (∀ n, FiniteCardinality n → X n)

def NecNumericalRigidity (σ : Type) [Ty σ] : Prop := □ (NumericalRigidity σ)

end Classicism.P
