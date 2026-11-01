import Mathlib.Order.Basic
import Mathlib.Data.Countable.Basic
import Classicism.Completeness.Reserve
import Classicism.Completeness.ObjectLemmas

/-!
# Canonical worlds

Bacon, *A Philosophical Introduction to Higher-Order Logics*, Definition 18.8, for the
paper's relational types. A **world** is a language, `Sig` with a roomy set `S` of reserve
constants, together with a theory `Γ` in that language that is consistent (with `C`),
complete for the language, and witnessed: every existential sentence in it has a closed
instance in the language. Accessibility is literal: `w ≤ v` when every sentence boxed in
`w` is in `v`. It is a preorder by `T` and `4`, and it includes languages, since `□(c = c)`
is in `w` for each constant `c` of `w`'s language.

The worlds and this preorder are the category of the canonical intensional action model;
there is at most one arrow between two objects.

INTERFACE (31 October 2026): the definitions and statements are fixed; the proofs are to be
supplied (workstream W1a). Change a statement only after reporting why. Lemmas may be
added freely.
-/

namespace Classicism.Meta

namespace Completeness

open Term

variable {Sig : Signature}

/-- A canonical world: a roomy language and a maximal consistent witnessed theory in it. -/
structure World (Sig : Signature) where
  /-- The reserve constants of the world's language. -/
  S : Set Reserve
  /-- Infinitely many reserve constants are left unused at every type. -/
  roomy : Roomy S
  /-- The world's theory. -/
  Γ : Set (Sentence (ext Sig))
  /-- Its sentences are in its language. -/
  lang : ∀ p ∈ Γ, InLang S p
  /-- It is consistent with `C`. -/
  consistent : AxiomSet.Consistent (fun p => p ∈ Γ)
  /-- It is complete for its language. -/
  complete : ∀ p : Sentence (ext Sig), InLang S p → p ∈ Γ ∨ neg p ∈ Γ
  /-- It is witnessed: an existential sentence in it has a closed instance in the language. -/
  witnessed : ∀ {σ : Ty} (F : Term (ext Sig) [] (σ ⇒ RTy.t)), app (.ex σ) F ∈ Γ →
    ∃ a : Term (ext Sig) [] σ, InLang S a ∧ app F a ∈ Γ

namespace World

variable (w v u : World Sig)

/-- Accessibility: whatever is necessary at `w` is true at `v`. -/
def Le : Prop := ∀ p : Sentence (ext Sig), box p ∈ w.Γ → p ∈ v.Γ

theorem le_refl : w.Le w := by
  sorry

theorem le_trans {w v u : World Sig} : w.Le v → v.Le u → w.Le u := by
  sorry

instance : Preorder (World Sig) where
  le := Le
  le_refl := le_refl
  le_trans _ _ _ := le_trans

variable {w v}

/-! ### A world is a maximal theory of its language -/

/-- Deductive closure within the language. -/
theorem mem_of_theorem {p : Sentence (ext Sig)} (hp : InLang w.S p)
    (h : Theorem (C.axioms ∪ fun q => q ∈ w.Γ) p) : p ∈ w.Γ := by
  sorry

theorem mem_neg_iff {p : Sentence (ext Sig)} (hp : InLang w.S p) : neg p ∈ w.Γ ↔ p ∉ w.Γ := by
  sorry

theorem mem_conj_iff {p q : Sentence (ext Sig)} (hp : InLang w.S p) (hq : InLang w.S q) :
    conj p q ∈ w.Γ ↔ p ∈ w.Γ ∧ q ∈ w.Γ := by
  sorry

theorem mem_disj_iff {p q : Sentence (ext Sig)} (hp : InLang w.S p) (hq : InLang w.S q) :
    disj p q ∈ w.Γ ↔ p ∈ w.Γ ∨ q ∈ w.Γ := by
  sorry

theorem mem_all_iff {σ : Ty} {F : Term (ext Sig) [] (σ ⇒ RTy.t)} (hF : InLang w.S F) :
    app (.all σ) F ∈ w.Γ ↔ ∀ a : Term (ext Sig) [] σ, InLang w.S a → app F a ∈ w.Γ := by
  sorry

theorem mem_ex_iff {σ : Ty} {F : Term (ext Sig) [] (σ ⇒ RTy.t)} (hF : InLang w.S F) :
    app (.ex σ) F ∈ w.Γ ↔ ∃ a : Term (ext Sig) [] σ, InLang w.S a ∧ app F a ∈ w.Γ := by
  sorry

/-- Membership transfers along conversion, within the language. -/
theorem mem_conv {p q : Sentence (ext Sig)} (hpq : p ≡ q) (hq : InLang w.S q) (hp : p ∈ w.Γ) :
    q ∈ w.Γ := by
  sorry

theorem eq_refl {σ : Ty} {a : Term (ext Sig) [] σ} (ha : InLang w.S a) : eq' a a ∈ w.Γ := by
  sorry

theorem eq_symm {σ : Ty} {a b : Term (ext Sig) [] σ} (h : eq' a b ∈ w.Γ) : eq' b a ∈ w.Γ := by
  sorry

theorem eq_trans {σ : Ty} {a b c : Term (ext Sig) [] σ} (h₁ : eq' a b ∈ w.Γ) (h₂ : eq' b c ∈ w.Γ) :
    eq' a c ∈ w.Γ := by
  sorry

/-- Leibniz's Law within a world. -/
theorem mem_ll {σ : Ty} {a b : Term (ext Sig) [] σ} (F : Term (ext Sig) [] (σ ⇒ RTy.t))
    (hFb : InLang w.S F) (h : eq' a b ∈ w.Γ) (hFa : app F a ∈ w.Γ) : app F b ∈ w.Γ := by
  sorry

/-! ### Accessibility -/

/-- Accessible worlds have larger languages. -/
theorem inLang_of_le (h : w ≤ v) {Γ : Ctx} {σ : Ty} {t : Term (ext Sig) Γ σ}
    (ht : InLang w.S t) : InLang v.S t := by
  sorry

/-- Identities persist along accessibility. -/
theorem eq_of_le (h : w ≤ v) {σ : Ty} {a b : Term (ext Sig) [] σ} (hab : eq' a b ∈ w.Γ) :
    eq' a b ∈ v.Γ := by
  sorry

/-- **The successor lemma** (Proposition 18.3 of the book): a sentence of the language that
is not necessary at `w` is false at some accessible world. -/
theorem exists_le_of_not_box [Countable Sig.Const] {p : Sentence (ext Sig)} (hp : InLang w.S p)
    (h : box p ∉ w.Γ) : ∃ v : World Sig, w ≤ v ∧ neg p ∈ v.Γ := by
  sorry

end World

/-- **Lindenbaum–Henkin**: an axiom set consistent with `C` is included in some world. -/
theorem exists_world [Countable Sig.Const] {Ax : AxiomSet Sig} (h : AxiomSet.Consistent Ax) :
    ∃ w : World Sig, ∀ a, AxiomSet.lift Ax a → a ∈ w.Γ := by
  sorry

end Completeness

end Classicism.Meta
