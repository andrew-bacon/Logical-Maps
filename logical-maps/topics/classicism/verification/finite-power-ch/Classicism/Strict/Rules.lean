import Classicism.Strict.Quantifier

/-!
# One lemma per proof rule

Appendix A turns a derivation of `P` in `H` into a derivation of `(λv̄. P) = (λv̄. ⊤)` from
the identities, by induction on the derivation: one calculation for each axiom scheme and
each rule. `H` is a Hilbert system, so its derivations have no hypotheses. A Lean proof term
is a natural deduction, and `fun h => …` puts hypotheses in scope, so the induction
hypothesis is carried in sequent form,

    (λv̄. Γ → P) = (λv̄. ⊤)        with `Γ` the conjunction of the hypotheses in scope,

which is the shape the paper's own `Gen` already has (`P' → ∀u. Q` from `P' → Q`). The
natural-deduction presentation of `C`, whose special rule takes premises `P ⊢ Q` and
`Q ⊢ P` with no side premises, is the same idea from the other direction: that side
condition is the gate.

This file holds the propositional part: for each way a proof term can be built from
hypotheses, implication and negation, the lemma that carries the induction through. They are
stated for elements `G A B` of an arbitrary algebra `BA τ`, and the transformer uses them at
`τ := v̄ → Prop` with `G := fun v̄ => Γ`, where the operations unfold by β to the pointwise
ones. Each is modus ponens against a tautology that `boolean_eq` proves in that algebra.

Write `G ⊩ A` for `imp G A = top`.
-/

namespace Classicism.Strict.BA

variable {τ : Type} [BA τ]

/-- `G ⊩ A`: the sequent `Γ ⊢ A`, as an identity in the algebra. -/
abbrev Seq (G A : τ) : Prop := imp G A = top

@[inherit_doc] scoped infix:25 " ⊩ " => Seq

/-- Modus ponens on identities with `⊤`: the engine of every rule below. Appendix A's
inductive step (i). -/
theorem mp_top {P Q : τ} (h₁ : imp P Q = top) (h₂ : P = top) : Q = top :=
  calc Q = (bot ⊔ Q) := (bot_join Q).symm
    _ = ((∼ top) ⊔ Q) := by rw [compl_top]
    _ = ((∼ P) ⊔ Q) := by rw [h₂]
    _ = top := h₁

/-! ### Structural rules -/

/-- The most recent hypothesis. -/
theorem rule_hyp (G H : τ) : G ⊓ H ⊩ H := by show _ = _; boolean_eq

/-- Weakening: what held before a hypothesis was added still holds. -/
theorem rule_weaken {G A : τ} (H : τ) (h : G ⊩ A) : G ⊓ H ⊩ A :=
  mp_top (by boolean_eq : imp (imp G A) (imp (G ⊓ H) A) = top) h

/-- A theorem holds under any hypotheses. -/
theorem rule_const (G : τ) {S : τ} (h : S = top) : G ⊩ S :=
  mp_top (by boolean_eq : imp S (imp G S) = top) h

/-- Leaving the empty context: `⊤ ⊩ A` is `A = ⊤`. -/
theorem of_seq_top {A : τ} (h : top ⊩ A) : A = top :=
  mp_top (by boolean_eq : imp (imp top A) A = top) h

/-! ### Implication and negation -/

/-- `fun h : H => b`. -/
theorem rule_imp_intro {G H B : τ} (h : G ⊓ H ⊩ B) : G ⊩ imp H B :=
  mp_top (by boolean_eq : imp (imp (G ⊓ H) B) (imp G (imp H B)) = top) h

/-- Application of a proof to a proof. -/
theorem rule_imp_elim {G A B : τ} (h₁ : G ⊩ imp A B) (h₂ : G ⊩ A) : G ⊩ B :=
  mp_top (mp_top (by boolean_eq : imp (imp G (imp A B)) (imp (imp G A) (imp G B)) = top) h₁) h₂

/-- `fun h : H => (b : False)`, which proves `¬H`. -/
theorem rule_not_intro {G H : τ} (h : G ⊓ H ⊩ bot) : G ⊩ ∼ H :=
  mp_top (by boolean_eq : imp (imp (G ⊓ H) bot) (imp G (∼ H)) = top) h

/-- Application of a proof of `¬A` to a proof of `A`. -/
theorem rule_not_elim {G A : τ} (h₁ : G ⊩ ∼ A) (h₂ : G ⊩ A) : G ⊩ bot :=
  mp_top (mp_top (by boolean_eq : imp (imp G (∼ A)) (imp (imp G A) (imp G bot)) = top) h₁) h₂

/-! ### The quantifier rules, in their Boolean part

`UI` is an absorption identity and `Gen` a distribution identity; what is left of each rule
once that identity has been applied is Boolean. -/

/-- If `A` absorbs `All` on the join side, then `All` entails `A`. With Absorption-∨∀ this
is application of a proof of `∀y. Fy` to a term. -/
theorem rule_absorb {G A All : τ} (ha : (A ⊔ All) = A) (h : G ⊩ All) : G ⊩ A :=
  have key : imp (imp G All) (imp G (A ⊔ All)) = top := by boolean_eq
  have h' : G ⊩ A ⊔ All := mp_top key h
  by rw [ha] at h'; exact h'

/-! ### Equivalence -/

/-- Appendix A, Proposition A.3: from `(A ↔ B) = ⊤` to `A = B`. At `τ := v̄ → Prop` this is
the rule of Equivalence in its bundled form, `λv̄.A = λv̄.B`, which is why a `funext` around
a `propext` needs no separate treatment. -/
theorem eq_of_iff_top {A B : τ} (h : iff A B = top) : A = B :=
  have key : (A ⊓ iff A B) = (B ⊓ iff A B) := by boolean_eq
  calc A = (A ⊓ top) := (meet_top A).symm
    _ = (A ⊓ iff A B) := by rw [h]
    _ = (B ⊓ iff A B) := key
    _ = (B ⊓ top) := by rw [h]
    _ = B := meet_top B

/-- `Iff.intro` on two closed lambdas. -/
theorem iff_top_of_imps {A B : τ} (h₁ : imp A B = top) (h₂ : imp B A = top) : iff A B = top :=
  mp_top (mp_top (by boolean_eq : imp (imp A B) (imp (imp B A) (iff A B)) = top) h₁) h₂

end Classicism.Strict.BA

/-! ### The tactic, between λ-terms

The same tactic, run in the algebra `σ → ρ → Prop`, proves an identity between λ-terms.
This is the "λ-level Booleanism" that Appendix A invokes under `λv̄`. -/

namespace Classicism.Strict

example {σ ρ : Type} [Ty σ] [Ty ρ] (F G : σ → ρ → Prop) :
    (fun x u => F x u ∧ (G x u ∨ ¬ G x u)) = (fun x u => ¬ ¬ F x u) := by
  boolean_eq

example : (fun a b : Prop => imp a (imp b (a ∧ b))) = (fun _ _ => Top) := by boolean_eq

end Classicism.Strict
