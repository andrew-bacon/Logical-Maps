import Classicism.Syntax.Entailment

/-!
# The object-language facts the completeness proof uses

Theorems of `C`, in any signature, about closed terms: the modal logic of `□` that makes
the canonical accessibility relation a preorder and lets a missing box be refuted at a
successor; the Necessity of Identity, which makes identities persist along accessibility;
and Intensionality, which makes the canonical inclusion of term classes into intensions
injective.

INTERFACE (31 October 2026): the statements are fixed; the proofs are to be supplied
(workstream W1b). Change a statement only after reporting why.
-/

namespace Classicism.Meta

namespace Completeness

variable {Sig : Signature}

open Term

/-- `K`: `□(p → q) → □p → □q`. -/
theorem box_K (p q : Sentence Sig) :
    C.Theorem (imp (box (imp p q)) (imp (box p) (box q))) := by
  sorry

/-- `T`: `□p → p`. -/
theorem box_T (p : Sentence Sig) : C.Theorem (imp (box p) p) := by
  sorry

/-- `4`: `□p → □□p`. -/
theorem box_4 (p : Sentence Sig) : C.Theorem (imp (box p) (box (box p))) := by
  sorry

/-- The Necessity of Identity, for closed terms of any type: `a = b → □(a = b)`. -/
theorem nec_identity {σ : Ty} (a b : Term Sig [] σ) :
    C.Theorem (imp (eq' a b) (box (eq' a b))) := by
  sorry

/-- Intensionality at a relational type: `a = b ↔ □(a ≡_ρ b)`, coextensiveness at `ρ`
being, at `t`, `↔`, and at `σ → ρ`, `λX Y. ∀z. X z ≡_ρ Y z` (its δ-unfolding). -/
theorem intensionality {ρ : RTy} (a b : Term Sig [] ρ) :
    C.Theorem (iff (eq' a b) (box (app (app (coextR ρ) a) b))) := by
  sorry

end Completeness

end Classicism.Meta
