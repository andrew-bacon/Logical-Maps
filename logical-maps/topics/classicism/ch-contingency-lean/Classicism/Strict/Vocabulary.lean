import Classicism.Strict.Algebra

/-!
# The strict layer: the Boolean algebra of propositions, from six axioms

This file is the target language of the Appendix A transformer, and it obeys the **strict
policy**: `propext` and `funext` are banned outright. Nothing here may use Logical
Equivalence in any form. The only inputs are

* the eleven closed identities of `Classicism.Axiomatization`, and
* Leibniz's Law, which in Lean is `congrArg`, `congrFun`, `rw` and `calc`.

Not even `em` is used: excluded middle is already encoded in the two Dissolution
identities, so every theorem below reports only the Boolean axioms it actually consumes.
`#classicism_strict` in `Classicism/Check.lean` enforces the policy.

## `⊤` and `⊥`

The paper defines them in Figure 1 as

    ⊤ := (∀p. p) ∨ ¬(∀p. p)        ⊥ := (∀p. p) ∧ ¬(∀p. p)

which is ungainly but deliberate: they are chosen so that they can be written, and shown
to be the bounds, in the Booleanism section, before any quantifier identity is available.
The shape is what matters. Because `⊤` is *some* `q ∨ ¬q` with `q` closed, Dissolution-∧∨
gives `p ∧ ⊤ = p` immediately, and dually for `⊥`.

This is also why the strict layer cannot reuse the rest of the library's `□p := (p = True)`.
No axiom mentions Lean's `True`, and an identity can only enter a proof from an axiom,
from `rfl`, from congruence on identities already held, or from `propext`. So
`(q ∨ ¬q) = True` is not derivable here, and the strict layer keeps its own `⊤`.

## The programme

The six Boolean Identities are Huntington's axioms for a Boolean algebra: two commutative
operations, each distributing over the other, with bounds and complements. Associativity
is **not** among them and has to be derived, which is the classic part of the argument and
runs through a cancellation lemma. The development below is the standard one, in the order
bounds, complements, idempotence, annihilation, absorption, cancellation, associativity,
uniqueness of complements, double negation, De Morgan.

Names follow the lattice, `meet` for `∧`, `join` for `∨`, `compl` for `¬`, both to say
what the file is about and to stay clear of the `_eq` lemmas in `Classicism/Booleanism.lean`,
which prove the same things the other way, by one gated use of Equivalence each.
-/

namespace Classicism.Strict

open Classicism.Axiomatic

/-- The paper's `⊤`, Figure 1. -/
abbrev Top : Prop := everything ∨ ¬ everything

/-- The paper's `⊥`, Figure 1. -/
abbrev Bot : Prop := everything ∧ ¬ everything

/-! ### The defined connectives

`imp` and `iff` are the paper's Figure 1 abbreviations, defined in `Classicism/Core.lean`.
The strict layer must use them rather than Lean's `→` and `Iff`, because those are a
primitive arrow and an inductive and no axiom connects either to the Boolean structure.
This is the same point as `True` above. -/

/-- Necessity in the strict vocabulary: identity with the paper's `⊤` rather than with
Lean's `True`. This is what `Classicism.Box` translates to. -/
abbrev Box (p : Prop) : Prop := p = Top

/-- Possibility likewise, distinctness from the paper's `⊥`. -/
abbrev Dia (p : Prop) : Prop := ¬ (p = Bot)

/-! ### The laws at type `t`

Every law below is the corresponding law of `Classicism/Algebra.lean`, which is proved
once for an arbitrary algebra presented by the six Boolean Identities, read at the
instance `BA Prop`, whose six fields are the six axioms verbatim. They are restated here
with Lean's `∧`, `∨`, `¬` so that `rw` can use them on ordinary propositional goals. The
derivations themselves, Huntington's, are in that file. -/

theorem meet_comm (p q : Prop) : (p ∧ q) = (q ∧ p) := BA.meet_comm p q

theorem join_comm (p q : Prop) : (p ∨ q) = (q ∨ p) := BA.join_comm p q

theorem meet_join_distrib (p q r : Prop) : (p ∧ (q ∨ r)) = ((p ∧ q) ∨ (p ∧ r)) :=
  BA.meet_join_distrib p q r

theorem join_meet_distrib (p q r : Prop) : (p ∨ (q ∧ r)) = ((p ∨ q) ∧ (p ∨ r)) :=
  BA.join_meet_distrib p q r

theorem meet_em (p q : Prop) : (p ∧ (q ∨ ¬ q)) = p := BA.meet_em p q

theorem join_contra (p q : Prop) : (p ∨ (q ∧ ¬ q)) = p := BA.join_contra p q

theorem meet_top (p : Prop) : (p ∧ Top) = p := BA.meet_top p

theorem join_bot (p : Prop) : (p ∨ Bot) = p := BA.join_bot p

theorem top_meet (p : Prop) : (Top ∧ p) = p := BA.top_meet p

theorem bot_join (p : Prop) : (Bot ∨ p) = p := BA.bot_join p

theorem join_compl (p : Prop) : (p ∨ ¬ p) = Top := BA.join_compl p

theorem meet_compl (p : Prop) : (p ∧ ¬ p) = Bot := BA.meet_compl p

theorem compl_join_self (p : Prop) : ((¬ p) ∨ p) = Top := BA.compl_join_self p

theorem compl_meet_self (p : Prop) : ((¬ p) ∧ p) = Bot := BA.compl_meet_self p

theorem join_idem (p : Prop) : (p ∨ p) = p := BA.join_idem p

theorem meet_idem (p : Prop) : (p ∧ p) = p := BA.meet_idem p

theorem join_top (p : Prop) : (p ∨ Top) = Top := BA.join_top p

theorem meet_bot (p : Prop) : (p ∧ Bot) = Bot := BA.meet_bot p

theorem top_join (p : Prop) : (Top ∨ p) = Top := BA.top_join p

theorem bot_meet (p : Prop) : (Bot ∧ p) = Bot := BA.bot_meet p

theorem join_absorb (p q : Prop) : (p ∨ (p ∧ q)) = p := BA.join_absorb p q

theorem meet_absorb (p q : Prop) : (p ∧ (p ∨ q)) = p := BA.meet_absorb p q

theorem eq_of_meet_eq {p q r : Prop}
    (h₁ : (p ∧ q) = (p ∧ r)) (h₂ : ((¬ p) ∧ q) = ((¬ p) ∧ r)) : q = r := BA.eq_of_meet_eq h₁ h₂

theorem join_assoc (p q r : Prop) : (p ∨ (q ∨ r)) = ((p ∨ q) ∨ r) := BA.join_assoc p q r

/-- The dual cancellation lemma, which is what associativity of `∧` needs. -/
theorem eq_of_join_eq {p q r : Prop}
    (h₁ : (p ∨ q) = (p ∨ r)) (h₂ : ((¬ p) ∨ q) = ((¬ p) ∨ r)) : q = r := BA.eq_of_join_eq h₁ h₂

theorem meet_assoc (p q r : Prop) : (p ∧ (q ∧ r)) = ((p ∧ q) ∧ r) := BA.meet_assoc p q r

theorem compl_unique {p q : Prop} (hj : (p ∨ q) = Top) (hm : (p ∧ q) = Bot) : q = ¬ p :=
  BA.compl_unique hj hm

theorem compl_compl (p : Prop) : (¬ ¬ p) = p := BA.compl_compl p

theorem compl_join (p q : Prop) : (¬ (p ∨ q)) = ((¬ p) ∧ (¬ q)) := BA.compl_join p q

theorem compl_meet (p q : Prop) : (¬ (p ∧ q)) = ((¬ p) ∨ (¬ q)) := BA.compl_meet p q

/-- `¬⊤ = ⊥` and `¬⊥ = ⊤`, closing the algebra: each bound is the other's complement. -/
theorem compl_top : (¬ Top) = Bot := BA.compl_top

theorem compl_bot : (¬ Bot) = Top := BA.compl_bot

/-- `l ∧ (q ∧ r) = (l ∧ q) ∧ (l ∧ r)`: a conjunct duplicates over `∧`, as it distributes
over `∨`. -/
theorem meet_meet_split (l q r : Prop) : (l ∧ (q ∧ r)) = ((l ∧ q) ∧ (l ∧ r)) :=
  BA.meet_meet_split l q r

/-- `l ∧ ¬q = l ∧ ¬(l ∧ q)`: under the conjunct `l`, the complement of `q` and the
complement of `l ∧ q` agree. This is what lets the recursion pass a negation. -/
theorem relative_compl (l q : Prop) : (l ∧ ¬ q) = (l ∧ ¬ (l ∧ q)) := BA.relative_compl l q

/-- Base case of the recursion at a positive literal: `a ∧ a = a ∧ ⊤`. -/
theorem meet_self_eq_meet_top (a : Prop) : (a ∧ a) = (a ∧ Top) := BA.meet_self_eq_meet_top a

/-- Base case at a negative literal: `¬a ∧ a = ¬a ∧ ⊥`. -/
theorem compl_meet_eq_meet_bot (a : Prop) : ((¬ a) ∧ a) = ((¬ a) ∧ Bot) :=
  BA.compl_meet_eq_meet_bot a

end Classicism.Strict
