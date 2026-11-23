import Classicism.Syntax.Derivation

/-!
# Classicism, as a theory

Classicism is `Derivable Logical`: `H` closed under Subst, with Existence at `e` as its one
axiom beyond the rules. This module names it, `C.axioms`, and its existentially neutral
variant `C.axiomsMinus` (the paper's `C⁻`, nn. 12–13), with `C.Derivable`, `C.Theorem`
and their `Minus` forms.

It also states the **eleven closed identities** of Figures 2 and 3 as sentences, in de
Bruijn syntax (`v0` the innermost bound variable, `v1` the next out, `v2` the next), as
the set `C.identities`. Appendix A of *Classicism* shows they axiomatize the theory over
`H`; here they are theorems of `Derivable Logical`, each a Subst at the hole
`λ… P = λ… ⬚` from the two derivations `P ⊢ Q`, `Q ⊢ P` in `H`, and the axiomatization is
a theorem to be proved, not a definition.
-/

namespace Classicism.Meta

variable {Sig : Signature}

namespace C

open Term

/-! ### The six Boolean Identities, Figure 2 -/

/-- `(λpq. p ∧ q) = (λpq. q ∧ p)`. -/
def commutativity_and : Sentence Sig :=
  eq' (lam (lam (conj v1 v0))) (lam (lam (conj v0 v1)))
/-- `(λpq. p ∨ q) = (λpq. q ∨ p)`. -/
def commutativity_or : Sentence Sig :=
  eq' (lam (lam (disj v1 v0))) (lam (lam (disj v0 v1)))
/-- `(λpqr. p ∧ (q ∨ r)) = (λpqr. (p ∧ q) ∨ (p ∧ r))`. -/
def distribution_and_or : Sentence Sig :=
  eq' (lam (lam (lam (conj v2 (disj v1 v0)))))
      (lam (lam (lam (disj (conj v2 v1) (conj v2 v0)))))
/-- `(λpqr. p ∨ (q ∧ r)) = (λpqr. (p ∨ q) ∧ (p ∨ r))`. -/
def distribution_or_and : Sentence Sig :=
  eq' (lam (lam (lam (disj v2 (conj v1 v0)))))
      (lam (lam (lam (conj (disj v2 v1) (disj v2 v0)))))
/-- `(λpq. p ∧ (q ∨ ¬q)) = (λpq. p)`. -/
def dissolution_and_or : Sentence Sig :=
  eq' (lam (lam (conj v1 (disj v0 (neg v0))))) (lam (lam (v1 : Term Sig [Ty.t, Ty.t] Ty.t)))
/-- `(λpq. p ∨ (q ∧ ¬q)) = (λpq. p)`. -/
def dissolution_or_and : Sentence Sig :=
  eq' (lam (lam (disj v1 (conj v0 (neg v0))))) (lam (lam (v1 : Term Sig [Ty.t, Ty.t] Ty.t)))

/-! ### The five Classicist Identities, Figure 3, at a type `σ` -/

/-- The Identity Identity: `(λyz. y = z) = (λyz. ∀X. Xy ↔ Xz)`. -/
def identity_identity (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (eq' (v1 : Term Sig [σ, σ] σ) v0)))
      (lam (lam (forall' (σ := σ ⇒ RTy.t) (iff (app v0 v2) (app v0 v1)))))
/-- Absorption-∨∀: `(λXy. Xy ∨ ∀X) = (λXy. Xy)`. -/
def absorption_or_forall (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (disj (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0) (app (all σ) v1))))
      (lam (lam (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))
/-- Distribution-∨∀: `(λXp. p ∨ ∀X) = (λXp. ∀y. p ∨ Xy)`. -/
def distribution_or_forall (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (disj (v0 : Term Sig [Ty.t, σ ⇒ RTy.t] Ty.t) (app (all σ) v1))))
      (lam (lam (forall' (σ := σ) (disj v1 (app (v2 : Term Sig [σ, Ty.t, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))))
/-- Absorption-∧∃: `(λXy. Xy ∧ ∃X) = (λXy. Xy)`. -/
def absorption_and_exists (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (conj (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0) (app (ex σ) v1))))
      (lam (lam (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))
/-- Distribution-∧∃: `(λXp. p ∧ ∃X) = (λXp. ∃y. p ∧ Xy)`. -/
def distribution_and_exists (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (conj (v0 : Term Sig [Ty.t, σ ⇒ RTy.t] Ty.t) (app (ex σ) v1))))
      (lam (lam (exists' (σ := σ) (conj v1 (app (v2 : Term Sig [σ, Ty.t, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))))

/-- Existence at `e`: `∃x:e. x = x`, the logical axiom of `Derivation.lean`. -/
abbrev existence_e : Sentence Sig := Meta.existence_e

/-- The eleven identities, the Classicist ones at every type, as a set of sentences. -/
inductive identities : AxiomSet Sig
  | commutativity_and : identities commutativity_and
  | commutativity_or : identities commutativity_or
  | distribution_and_or : identities distribution_and_or
  | distribution_or_and : identities distribution_or_and
  | dissolution_and_or : identities dissolution_and_or
  | dissolution_or_and : identities dissolution_or_and
  | identity_identity (σ : Ty) : identities (identity_identity σ)
  | absorption_or_forall (σ : Ty) : identities (absorption_or_forall σ)
  | distribution_or_forall (σ : Ty) : identities (distribution_or_forall σ)
  | absorption_and_exists (σ : Ty) : identities (absorption_and_exists σ)
  | distribution_and_exists (σ : Ty) : identities (distribution_and_exists σ)

/-- The axioms of `C`: the logical axioms, Existence at `e`. -/
abbrev axioms : AxiomSet Sig := Logical
/-- The axioms of `C⁻`: none. -/
abbrev axiomsMinus : AxiomSet Sig := fun _ => False

theorem axioms.existence_e : axioms (Sig := Sig) existence_e := rfl

/-- Derivability in Classicism. -/
abbrev Derivable {Γ : Ctx} (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  Meta.Derivable axioms Δ p
/-- Derivability in `C⁻`. -/
abbrev DerivableMinus {Γ : Ctx} (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  Meta.Derivable axiomsMinus Δ p
/-- A theorem of Classicism. -/
abbrev Theorem (p : Sentence Sig) : Prop := Meta.Theorem axioms p
/-- A theorem of `C⁻`. -/
abbrev TheoremMinus (p : Sentence Sig) : Prop := Meta.Theorem axiomsMinus p

theorem Derivable.of_minus {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : DerivableMinus Δ p) : Derivable Δ p :=
  Meta.Derivable.mono (fun _ h => h.elim) h

end C

/-! ### Citing an axiom in the empty context -/

theorem Ren.ofEmpty_eq_id : (Ren.ofEmpty : Ren [] []) = Ren.id := by
  funext σ v; exact nomatch v

@[simp] theorem Term.close_nil {σ : Ty} (a : Term Sig [] σ) : a.close = a := by
  rw [Term.close, Ren.ofEmpty_eq_id, Term.rename_id]

/-- An axiom is a theorem. -/
theorem Derivable.axiom {Ax : AxiomSet Sig} {a : Sentence Sig} (h : Ax a) : Theorem Ax a := by
  have := Derivable.ax (Δ := ([] : List (Formula Sig []))) h
  rwa [Term.close_nil] at this

end Classicism.Meta
