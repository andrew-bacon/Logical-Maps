import Classicism.Results.Research.ExactLowerCorrespondence

/-!
# Fixed-type principles for the exact/at-least comparison

These aliases retain the definitions used by the proved research lemmas.
They concern type e only, matching the three existing map nodes. No
identification of exact zero with at-least zero is made.

GPT-6 Astra Pro (OpenAI), prompted by Andrew Bacon, 28 October 2026.
-/
namespace Classicism.P

/-- `necessary-lower-peano-e`. -/
def NecessaryLowerPeanoE : Prop := ExactLower.NecessaryLowerPeano e

/-- `exact-peano-e`. -/
def ExactPeanoE : Prop := ExactLower.ExactPeano e

/-- `exact-lower-finite-cardinality-bijection-e`: the relational bijection
includes the zero pair and is closed under synchronous successor. -/
def ExactLowerBijectionE : Prop := ExactLower.ExactLowerBijection e

end Classicism.P
