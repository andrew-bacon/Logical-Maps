import Classicism.Results.MathematicalContingency.NaturalCHContingency
import Classicism.Principles.ExactLower

/-! The CH map vocabulary, using the native Classicism library.
OpenAI Codex, prompted by Andrew Bacon, 29 October 2026.
The size parameter is a type parameter, never an object-language quantifier. -/
namespace Classicism.P
open Classicism.MathematicalContingency

/-- The two forcing algebras share one inaccessible size witness. -/
def BoundedCHForcingSetup (κ : Type) [Ty κ] : Prop :=
  ∃ (K : κ → Prop) (L : κ → κ → Prop),
    MPAt (CountableBitGraph e (OrdinalCarrier ((e → Prop) → Prop)) → Prop) K L ∧
    MPAt (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop) K L ∧
    StronglyInaccessible K L ∧
    NaturalPositiveRC (κ := κ) ∧ NaturalNegativeRC (κ := κ) ∧
    □ (RigidComprehension
      (CohenGraph e (OrdinalCarrier (OrdinalCarrier ((e → Prop) → Prop))) → Prop)) ∧
    NaturalCHChoice

def RigidLowerNatE : Prop := Rigid (@LowerNat e _)

/-- Cardinal CH on the lower-natural carrier and its rigid power. -/
def CardinalCHContingency : Prop :=
  (◇ (CardinalCH (@LowerNat e _) (MathematicalContingency.RigidPower (@LowerNat e _)))) ∧
  (◇ (¬ CardinalCH (@LowerNat e _) (MathematicalContingency.RigidPower (@LowerNat e _))))

end Classicism.P
