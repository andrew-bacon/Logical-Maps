import Classicism.Strict.Axiomatization

/-!
# Boolean algebras given by the six Boolean Identities

Appendix A reasons, at every step, about identities between **λ-terms**: its induction
hypothesis is `(λv̄. P) = (λv̄. ⊤)`, and "Booleanism" is invoked under the `λv̄`. Lean's
`funext` would turn a pointwise law into such an identity, but the strict policy bans it,
and rightly, since that is the rule ξ the paper avoids.

The way through is to notice that the six Boolean Identities are *closed* identities, so
they transfer to every relational type by Leibniz's Law alone:

* a `BA τ` is a type with `and`, `or`, `neg` and the six identities in closed form;
* `BA Prop` is the six axioms, verbatim;
* `BA (σ → τ)` takes each field from the field at `τ` by **one** `congrArg`.

Everything else, which is Huntington's derivation of a Boolean algebra from those six, is
then proved once, about elements `X Y Z : τ` of an arbitrary such algebra, by ordinary
equational reasoning. At `τ := v̄ → Prop` the operations unfold by β to the pointwise ones,
so a law proved here *is* the λ-level identity Appendix A needs, with no ξ anywhere.

Strict policy throughout: no `propext`, no `funext`, not even `em`.

Names follow the lattice, `meet` for `and`, `join` for `or`, `compl` for `neg`.
-/

namespace Classicism.Strict

open Classicism.Axiomatic

/-- A Boolean algebra presented by the six Boolean Identities of Figure 2, in closed,
λ-abstracted form. `unit` is an arbitrary element from which the bounds are built, as the
paper builds `⊤` and `⊥` from `∀p. p`. -/
class BA (τ : Type) : Type where
  /-- Conjunction at `τ`. -/
  and : τ → τ → τ
  /-- Disjunction at `τ`. -/
  or : τ → τ → τ
  /-- Negation at `τ`. -/
  neg : τ → τ
  /-- An arbitrary element, from which the bounds are built. -/
  unit : τ
  comm_and : (fun X Y => and X Y) = (fun X Y => and Y X)
  comm_or : (fun X Y => or X Y) = (fun X Y => or Y X)
  dist_and_or : (fun X Y Z => and X (or Y Z)) = (fun X Y Z => or (and X Y) (and X Z))
  dist_or_and : (fun X Y Z => or X (and Y Z)) = (fun X Y Z => and (or X Y) (or X Z))
  diss_and_or : (fun X Y => and X (or Y (neg Y))) = (fun X _ => X)
  diss_or_and : (fun X Y => or X (and Y (neg Y))) = (fun X _ => X)

/-- `∀p. p`, the proposition that everything holds. The paper's bounds are built from it. -/
abbrev everything : Prop := ∀ p : Prop, p

/-- At type `t` the six fields are the six axioms, verbatim. -/
instance instBAProp : BA Prop where
  and := And
  or := Or
  neg := Not
  unit := everything
  comm_and := commutativity_and
  comm_or := commutativity_or
  dist_and_or := distribution_and_or
  dist_or_and := distribution_or_and
  diss_and_or := dissolution_and_or
  diss_or_and := dissolution_or_and

/-- At `σ → τ` every field is one congruence step on the field at `τ`. No `funext`. The
guard `[Ty σ]` keeps the instances inside the relational type system: a `BA τ` exists
exactly when `τ` is `v̄ → Prop` for `R`-types `v̄`. -/
instance instBAArrow {σ τ : Type} [Ty σ] [BA τ] : BA (σ → τ) where
  and X Y := fun z => BA.and (X z) (Y z)
  or X Y := fun z => BA.or (X z) (Y z)
  neg X := fun z => BA.neg (X z)
  unit := fun _ => BA.unit
  comm_and := congrArg (fun (K : τ → τ → τ) (X Y : σ → τ) z => K (X z) (Y z)) BA.comm_and
  comm_or := congrArg (fun (K : τ → τ → τ) (X Y : σ → τ) z => K (X z) (Y z)) BA.comm_or
  dist_and_or :=
    congrArg (fun (K : τ → τ → τ → τ) (X Y Z : σ → τ) z => K (X z) (Y z) (Z z)) BA.dist_and_or
  dist_or_and :=
    congrArg (fun (K : τ → τ → τ → τ) (X Y Z : σ → τ) z => K (X z) (Y z) (Z z)) BA.dist_or_and
  diss_and_or := congrArg (fun (K : τ → τ → τ) (X Y : σ → τ) z => K (X z) (Y z)) BA.diss_and_or
  diss_or_and := congrArg (fun (K : τ → τ → τ) (X Y : σ → τ) z => K (X z) (Y z)) BA.diss_or_and

namespace BA

variable {τ : Type} [BA τ]

@[inherit_doc] scoped infixr:35 " ⊓ " => BA.and
@[inherit_doc] scoped infixr:30 " ⊔ " => BA.or
@[inherit_doc] scoped notation:max "∼" X:40 => BA.neg X

/-- The top of the algebra, `unit ⊔ ∼unit`. At `Prop` this is the paper's `⊤`. -/
abbrev top : τ := BA.unit ⊔ ∼ (BA.unit : τ)
/-- The bottom, `unit ⊓ ∼unit`. At `Prop` this is the paper's `⊥`. -/
abbrev bot : τ := BA.unit ⊓ ∼ (BA.unit : τ)
/-- Material implication, Figure 1. -/
abbrev imp (X Y : τ) : τ := ∼ X ⊔ Y
/-- The biconditional, Figure 1. -/
abbrev iff (X Y : τ) : τ := (∼ X ⊔ Y) ⊓ (∼ Y ⊔ X)

/-! ### The six identities, applied to elements

Each is the closed identity applied to its arguments by `congrFun`, which is Leibniz's Law.
These six lines are the only place the class fields are named. -/

theorem meet_comm (p q : τ) : (p ⊓ q) = (q ⊓ p) := congrFun (congrFun comm_and p) q
theorem join_comm (p q : τ) : (p ⊔ q) = (q ⊔ p) := congrFun (congrFun comm_or p) q
theorem meet_join_distrib (p q r : τ) : (p ⊓ (q ⊔ r)) = ((p ⊓ q) ⊔ (p ⊓ r)) :=
  congrFun (congrFun (congrFun dist_and_or p) q) r
theorem join_meet_distrib (p q r : τ) : (p ⊔ (q ⊓ r)) = ((p ⊔ q) ⊓ (p ⊔ r)) :=
  congrFun (congrFun (congrFun dist_or_and p) q) r
theorem meet_em (p q : τ) : (p ⊓ (q ⊔ ∼ q)) = p := congrFun (congrFun diss_and_or p) q
theorem join_contra (p q : τ) : (p ⊔ (q ⊓ ∼ q)) = p := congrFun (congrFun diss_or_and p) q

/-! ### The bounds -/

theorem meet_top (p : τ) : (p ⊓ top) = p := meet_em p BA.unit
theorem join_bot (p : τ) : (p ⊔ bot) = p := join_contra p BA.unit
theorem top_meet (p : τ) : (top ⊓ p) = p := by rw [meet_comm]; exact meet_top p
theorem bot_join (p : τ) : (bot ⊔ p) = p := by rw [join_comm]; exact join_bot p

/-! ### Complements

Every excluded middle is `⊤` and every contradiction is `⊥`: the bounds absorb them, and
commutativity turns the absorption around. -/

theorem join_compl (p : τ) : (p ⊔ ∼ p) = top :=
  calc (p ⊔ ∼ p) = ((p ⊔ ∼ p) ⊓ top) := (meet_top _).symm
    _ = (top ⊓ (p ⊔ ∼ p)) := meet_comm _ _
    _ = top := meet_em top p

theorem meet_compl (p : τ) : (p ⊓ ∼ p) = bot :=
  calc (p ⊓ ∼ p) = ((p ⊓ ∼ p) ⊔ bot) := (join_bot _).symm
    _ = (bot ⊔ (p ⊓ ∼ p)) := join_comm _ _
    _ = bot := join_contra bot p

theorem compl_join_self (p : τ) : ((∼ p) ⊔ p) = top := by
  rw [join_comm]; exact join_compl p

theorem compl_meet_self (p : τ) : ((∼ p) ⊓ p) = bot := by
  rw [meet_comm]; exact meet_compl p

/-! ### Idempotence -/

theorem join_idem (p : τ) : (p ⊔ p) = p :=
  calc (p ⊔ p) = ((p ⊔ p) ⊓ top) := (meet_top _).symm
    _ = ((p ⊔ p) ⊓ (p ⊔ ∼ p)) := by rw [join_compl]
    _ = (p ⊔ (p ⊓ ∼ p)) := (join_meet_distrib p p (∼ p)).symm
    _ = p := join_contra p p

theorem meet_idem (p : τ) : (p ⊓ p) = p :=
  calc (p ⊓ p) = ((p ⊓ p) ⊔ bot) := (join_bot _).symm
    _ = ((p ⊓ p) ⊔ (p ⊓ ∼ p)) := by rw [meet_compl]
    _ = (p ⊓ (p ⊔ ∼ p)) := (meet_join_distrib p p (∼ p)).symm
    _ = p := meet_em p p

/-! ### Annihilation -/

theorem join_top (p : τ) : (p ⊔ top) = top :=
  calc (p ⊔ top) = ((p ⊔ top) ⊓ top) := (meet_top _).symm
    _ = ((p ⊔ top) ⊓ (p ⊔ ∼ p)) := by rw [join_compl]
    _ = (p ⊔ (top ⊓ ∼ p)) := (join_meet_distrib p top (∼ p)).symm
    _ = (p ⊔ ∼ p) := by rw [top_meet]
    _ = top := join_compl p

theorem meet_bot (p : τ) : (p ⊓ bot) = bot :=
  calc (p ⊓ bot) = ((p ⊓ bot) ⊔ bot) := (join_bot _).symm
    _ = ((p ⊓ bot) ⊔ (p ⊓ ∼ p)) := by rw [meet_compl]
    _ = (p ⊓ (bot ⊔ ∼ p)) := (meet_join_distrib p bot (∼ p)).symm
    _ = (p ⊓ ∼ p) := by rw [bot_join]
    _ = bot := meet_compl p

theorem top_join (p : τ) : (top ⊔ p) = top := by rw [join_comm]; exact join_top p
theorem bot_meet (p : τ) : (bot ⊓ p) = bot := by rw [meet_comm]; exact meet_bot p

/-! ### Absorption -/

theorem join_absorb (p q : τ) : (p ⊔ (p ⊓ q)) = p :=
  calc (p ⊔ (p ⊓ q)) = ((p ⊓ top) ⊔ (p ⊓ q)) := by rw [meet_top]
    _ = (p ⊓ (top ⊔ q)) := (meet_join_distrib p top q).symm
    _ = (p ⊓ top) := by rw [top_join]
    _ = p := meet_top p

theorem meet_absorb (p q : τ) : (p ⊓ (p ⊔ q)) = p :=
  calc (p ⊓ (p ⊔ q)) = ((p ⊔ bot) ⊓ (p ⊔ q)) := by rw [join_bot]
    _ = (p ⊔ (bot ⊓ q)) := (join_meet_distrib p bot q).symm
    _ = (p ⊔ bot) := by rw [bot_meet]
    _ = p := join_bot p

/-! ### Cancellation, and associativity

`eq_of_meet_eq` is the step that makes associativity available: two propositions that
agree under `p` and under `∼p` are identical, because the two cases recombine by
distributivity over `p ⊔ ∼p = ⊤`. -/

theorem eq_of_meet_eq {p q r : τ}
    (h₁ : (p ⊓ q) = (p ⊓ r)) (h₂ : ((∼ p) ⊓ q) = ((∼ p) ⊓ r)) : q = r :=
  calc q = (q ⊓ top) := (meet_top q).symm
    _ = (q ⊓ (p ⊔ ∼ p)) := by rw [join_compl]
    _ = ((q ⊓ p) ⊔ (q ⊓ ∼ p)) := meet_join_distrib q p (∼ p)
    _ = ((p ⊓ q) ⊔ ((∼ p) ⊓ q)) := by rw [meet_comm q p, meet_comm q (∼ p)]
    _ = ((p ⊓ r) ⊔ ((∼ p) ⊓ r)) := by rw [h₁, h₂]
    _ = ((r ⊓ p) ⊔ (r ⊓ ∼ p)) := by rw [meet_comm p r, meet_comm (∼ p) r]
    _ = (r ⊓ (p ⊔ ∼ p)) := (meet_join_distrib r p (∼ p)).symm
    _ = (r ⊓ top) := by rw [join_compl]
    _ = r := meet_top r

theorem join_assoc (p q r : τ) : (p ⊔ (q ⊔ r)) = ((p ⊔ q) ⊔ r) := by
  refine eq_of_meet_eq (p := p) ?_ ?_
  · -- under `p` both sides collapse to `p`, by absorption
    calc (p ⊓ (p ⊔ (q ⊔ r))) = p := meet_absorb p (q ⊔ r)
      _ = (p ⊔ (p ⊓ r)) := (join_absorb p r).symm
      _ = ((p ⊓ (p ⊔ q)) ⊔ (p ⊓ r)) := by rw [meet_absorb]
      _ = (p ⊓ ((p ⊔ q) ⊔ r)) := (meet_join_distrib p (p ⊔ q) r).symm
  · -- under `∼p` the `p` disjunct vanishes on both sides
    calc ((∼ p) ⊓ (p ⊔ (q ⊔ r)))
        = (((∼ p) ⊓ p) ⊔ ((∼ p) ⊓ (q ⊔ r))) := meet_join_distrib _ p (q ⊔ r)
      _ = (bot ⊔ ((∼ p) ⊓ (q ⊔ r))) := by rw [compl_meet_self]
      _ = ((∼ p) ⊓ (q ⊔ r)) := bot_join _
      _ = (((∼ p) ⊓ q) ⊔ ((∼ p) ⊓ r)) := meet_join_distrib _ q r
      _ = ((bot ⊔ ((∼ p) ⊓ q)) ⊔ ((∼ p) ⊓ r)) := by rw [bot_join]
      _ = ((((∼ p) ⊓ p) ⊔ ((∼ p) ⊓ q)) ⊔ ((∼ p) ⊓ r)) := by rw [compl_meet_self]
      _ = (((∼ p) ⊓ (p ⊔ q)) ⊔ ((∼ p) ⊓ r)) := by rw [← meet_join_distrib]
      _ = ((∼ p) ⊓ ((p ⊔ q) ⊔ r)) := (meet_join_distrib _ (p ⊔ q) r).symm

/-- The dual cancellation lemma, which is what associativity of `⊓` needs. -/
theorem eq_of_join_eq {p q r : τ}
    (h₁ : (p ⊔ q) = (p ⊔ r)) (h₂ : ((∼ p) ⊔ q) = ((∼ p) ⊔ r)) : q = r :=
  calc q = (q ⊔ bot) := (join_bot q).symm
    _ = (q ⊔ (p ⊓ ∼ p)) := by rw [meet_compl]
    _ = ((q ⊔ p) ⊓ (q ⊔ ∼ p)) := join_meet_distrib q p (∼ p)
    _ = ((p ⊔ q) ⊓ ((∼ p) ⊔ q)) := by rw [join_comm q p, join_comm q (∼ p)]
    _ = ((p ⊔ r) ⊓ ((∼ p) ⊔ r)) := by rw [h₁, h₂]
    _ = ((r ⊔ p) ⊓ (r ⊔ ∼ p)) := by rw [join_comm p r, join_comm (∼ p) r]
    _ = (r ⊔ (p ⊓ ∼ p)) := (join_meet_distrib r p (∼ p)).symm
    _ = (r ⊔ bot) := by rw [meet_compl]
    _ = r := join_bot r

theorem meet_assoc (p q r : τ) : (p ⊓ (q ⊓ r)) = ((p ⊓ q) ⊓ r) := by
  refine eq_of_join_eq (p := p) ?_ ?_
  · -- under `p` both sides collapse to `p`, by absorption
    calc (p ⊔ (p ⊓ (q ⊓ r))) = p := join_absorb p (q ⊓ r)
      _ = (p ⊓ (p ⊔ r)) := (meet_absorb p r).symm
      _ = ((p ⊔ (p ⊓ q)) ⊓ (p ⊔ r)) := by rw [join_absorb]
      _ = (p ⊔ ((p ⊓ q) ⊓ r)) := (join_meet_distrib p (p ⊓ q) r).symm
  · -- under `∼p` the `p` conjunct vanishes on both sides
    calc ((∼ p) ⊔ (p ⊓ (q ⊓ r)))
        = (((∼ p) ⊔ p) ⊓ ((∼ p) ⊔ (q ⊓ r))) := join_meet_distrib _ p (q ⊓ r)
      _ = (top ⊓ ((∼ p) ⊔ (q ⊓ r))) := by rw [compl_join_self]
      _ = ((∼ p) ⊔ (q ⊓ r)) := top_meet _
      _ = (((∼ p) ⊔ q) ⊓ ((∼ p) ⊔ r)) := join_meet_distrib _ q r
      _ = ((top ⊓ ((∼ p) ⊔ q)) ⊓ ((∼ p) ⊔ r)) := by rw [top_meet]
      _ = ((((∼ p) ⊔ p) ⊓ ((∼ p) ⊔ q)) ⊓ ((∼ p) ⊔ r)) := by rw [compl_join_self]
      _ = (((∼ p) ⊔ (p ⊓ q)) ⊓ ((∼ p) ⊔ r)) := by rw [← join_meet_distrib]
      _ = ((∼ p) ⊔ ((p ⊓ q) ⊓ r)) := (join_meet_distrib _ (p ⊓ q) r).symm

/-! ### Uniqueness of complements, double negation, De Morgan -/

theorem compl_unique {p q : τ} (hj : (p ⊔ q) = top) (hm : (p ⊓ q) = bot) : q = ∼ p :=
  have hq : q = ((∼ p) ⊓ q) :=
    calc q = (q ⊓ top) := (meet_top q).symm
      _ = (q ⊓ (p ⊔ ∼ p)) := by rw [join_compl]
      _ = ((q ⊓ p) ⊔ (q ⊓ ∼ p)) := meet_join_distrib q p (∼ p)
      _ = (bot ⊔ (q ⊓ ∼ p)) := by rw [meet_comm q p, hm]
      _ = (q ⊓ ∼ p) := bot_join _
      _ = ((∼ p) ⊓ q) := meet_comm _ _
  have hnp : (∼ p) = ((∼ p) ⊓ q) :=
    calc (∼ p) = ((∼ p) ⊓ top) := (meet_top _).symm
      _ = ((∼ p) ⊓ (p ⊔ q)) := by rw [hj]
      _ = (((∼ p) ⊓ p) ⊔ ((∼ p) ⊓ q)) := meet_join_distrib _ p q
      _ = (bot ⊔ ((∼ p) ⊓ q)) := by rw [compl_meet_self]
      _ = ((∼ p) ⊓ q) := bot_join _
  hq.trans hnp.symm

theorem compl_compl (p : τ) : (∼ ∼ p) = p :=
  (compl_unique (p := ∼ p) (compl_join_self p) (compl_meet_self p)).symm

theorem compl_join (p q : τ) : (∼ (p ⊔ q)) = ((∼ p) ⊓ (∼ q)) :=
  have hj : ((p ⊔ q) ⊔ ((∼ p) ⊓ (∼ q))) = top :=
    calc ((p ⊔ q) ⊔ ((∼ p) ⊓ (∼ q)))
        = (((p ⊔ q) ⊔ ∼ p) ⊓ ((p ⊔ q) ⊔ ∼ q)) := join_meet_distrib _ _ _
      _ = ((∼ p ⊔ (p ⊔ q)) ⊓ ((p ⊔ q) ⊔ ∼ q)) := by rw [join_comm (p ⊔ q) (∼ p)]
      _ = (((∼ p ⊔ p) ⊔ q) ⊓ ((p ⊔ q) ⊔ ∼ q)) := by rw [join_assoc]
      _ = ((top ⊔ q) ⊓ ((p ⊔ q) ⊔ ∼ q)) := by rw [compl_join_self]
      _ = (top ⊓ ((p ⊔ q) ⊔ ∼ q)) := by rw [top_join]
      _ = ((p ⊔ q) ⊔ ∼ q) := top_meet _
      _ = ((q ⊔ p) ⊔ ∼ q) := by rw [join_comm p q]
      _ = (∼ q ⊔ (q ⊔ p)) := join_comm _ _
      _ = ((∼ q ⊔ q) ⊔ p) := join_assoc _ _ _
      _ = (top ⊔ p) := by rw [compl_join_self]
      _ = top := top_join p
  have hm : ((p ⊔ q) ⊓ ((∼ p) ⊓ (∼ q))) = bot :=
    calc ((p ⊔ q) ⊓ ((∼ p) ⊓ (∼ q)))
        = (((∼ p) ⊓ (∼ q)) ⊓ (p ⊔ q)) := meet_comm _ _
      _ = ((((∼ p) ⊓ (∼ q)) ⊓ p) ⊔ (((∼ p) ⊓ (∼ q)) ⊓ q)) := meet_join_distrib _ p q
      _ = (((∼ p) ⊓ ((∼ q) ⊓ p)) ⊔ (((∼ p) ⊓ (∼ q)) ⊓ q)) := by rw [← meet_assoc]
      _ = (((∼ p) ⊓ (p ⊓ (∼ q))) ⊔ (((∼ p) ⊓ (∼ q)) ⊓ q)) := by rw [meet_comm (∼ q) p]
      _ = ((((∼ p) ⊓ p) ⊓ (∼ q)) ⊔ (((∼ p) ⊓ (∼ q)) ⊓ q)) := by rw [meet_assoc]
      _ = ((bot ⊓ (∼ q)) ⊔ (((∼ p) ⊓ (∼ q)) ⊓ q)) := by rw [compl_meet_self]
      _ = (bot ⊔ (((∼ p) ⊓ (∼ q)) ⊓ q)) := by rw [bot_meet]
      _ = (((∼ p) ⊓ (∼ q)) ⊓ q) := bot_join _
      _ = ((∼ p) ⊓ ((∼ q) ⊓ q)) := by rw [← meet_assoc]
      _ = ((∼ p) ⊓ bot) := by rw [compl_meet_self]
      _ = bot := meet_bot _
  (compl_unique hj hm).symm

theorem compl_meet (p q : τ) : (∼ (p ⊓ q)) = ((∼ p) ⊔ (∼ q)) :=
  have hnp : ((p ⊓ q) ⊔ ∼ p) = ((∼ p) ⊔ q) :=
    calc ((p ⊓ q) ⊔ ∼ p) = ((∼ p) ⊔ (p ⊓ q)) := join_comm _ _
      _ = (((∼ p) ⊔ p) ⊓ ((∼ p) ⊔ q)) := join_meet_distrib _ p q
      _ = (top ⊓ ((∼ p) ⊔ q)) := by rw [compl_join_self]
      _ = ((∼ p) ⊔ q) := top_meet _
  have hj : ((p ⊓ q) ⊔ ((∼ p) ⊔ (∼ q))) = top :=
    calc ((p ⊓ q) ⊔ ((∼ p) ⊔ (∼ q))) = (((p ⊓ q) ⊔ ∼ p) ⊔ ∼ q) := join_assoc _ _ _
      _ = (((∼ p) ⊔ q) ⊔ ∼ q) := by rw [hnp]
      _ = ((∼ p) ⊔ (q ⊔ ∼ q)) := (join_assoc _ _ _).symm
      _ = ((∼ p) ⊔ top) := by rw [join_compl]
      _ = top := join_top _
  have hm : ((p ⊓ q) ⊓ ((∼ p) ⊔ (∼ q))) = bot :=
    calc ((p ⊓ q) ⊓ ((∼ p) ⊔ (∼ q)))
        = (((p ⊓ q) ⊓ ∼ p) ⊔ ((p ⊓ q) ⊓ ∼ q)) := meet_join_distrib _ _ _
      _ = ((p ⊓ (q ⊓ ∼ p)) ⊔ (p ⊓ (q ⊓ ∼ q))) := by rw [← meet_assoc, ← meet_assoc]
      _ = ((p ⊓ ((∼ p) ⊓ q)) ⊔ (p ⊓ (q ⊓ ∼ q))) := by rw [meet_comm q (∼ p)]
      _ = (((p ⊓ ∼ p) ⊓ q) ⊔ (p ⊓ (q ⊓ ∼ q))) := by rw [meet_assoc]
      _ = ((bot ⊓ q) ⊔ (p ⊓ bot)) := by rw [meet_compl, meet_compl]
      _ = (bot ⊔ bot) := by rw [bot_meet, meet_bot]
      _ = bot := bot_join _
  (compl_unique hj hm).symm

/-- `∼⊤ = ⊥` and `∼⊥ = ⊤`, closing the algebra: each bound is the other's complement. -/
theorem compl_top : (∼ (top : τ)) = bot :=
  (compl_unique (p := top) (q := bot) (top_join bot) (top_meet bot)).symm

theorem compl_bot : (∼ (bot : τ)) = top :=
  (compl_unique (p := bot) (q := top) (bot_join top) (bot_meet top)).symm

/-! ### Lemmas the tautology tactic needs

`Classicism/Tautology.lean` decides identities between `⊓`/`⊔`/`∼` formulas by Shannon
expansion. Three laws carry the recursion: a conjunct distributes into a conjunction as
well as into a disjunction, and a conjunct may be pushed under a negation as a *relative*
complement. The last is the only non-obvious one. -/

/-- `l ⊓ (q ⊓ r) = (l ⊓ q) ⊓ (l ⊓ r)`: a conjunct duplicates over `⊓`, as it distributes
over `⊔`. -/
theorem meet_meet_split (l q r : τ) : (l ⊓ (q ⊓ r)) = ((l ⊓ q) ⊓ (l ⊓ r)) :=
  (calc ((l ⊓ q) ⊓ (l ⊓ r))
      = (l ⊓ (q ⊓ (l ⊓ r))) := (meet_assoc l q (l ⊓ r)).symm
    _ = (l ⊓ ((q ⊓ l) ⊓ r)) := congrArg (fun x => l ⊓ x) (meet_assoc q l r)
    _ = (l ⊓ ((l ⊓ q) ⊓ r)) := congrArg (fun x => l ⊓ (x ⊓ r)) (meet_comm q l)
    _ = (l ⊓ (l ⊓ (q ⊓ r))) := congrArg (fun x => l ⊓ x) (meet_assoc l q r).symm
    _ = ((l ⊓ l) ⊓ (q ⊓ r)) := meet_assoc l l (q ⊓ r)
    _ = (l ⊓ (q ⊓ r)) := congrArg (fun x => x ⊓ (q ⊓ r)) (meet_idem l)).symm

/-- `l ⊓ ∼q = l ⊓ ∼(l ⊓ q)`: under the conjunct `l`, the complement of `q` and the
complement of `l ⊓ q` agree. This is what lets the recursion pass a negation. -/
theorem relative_compl (l q : τ) : (l ⊓ ∼ q) = (l ⊓ ∼ (l ⊓ q)) :=
  calc (l ⊓ ∼ q) = (bot ⊔ (l ⊓ ∼ q)) := (bot_join _).symm
    _ = ((l ⊓ ∼ l) ⊔ (l ⊓ ∼ q)) := by rw [meet_compl]
    _ = (l ⊓ ((∼ l) ⊔ (∼ q))) := (meet_join_distrib l (∼ l) (∼ q)).symm
    _ = (l ⊓ ∼ (l ⊓ q)) := by rw [compl_meet]

/-- Base case of the recursion at a positive literal: `a ⊓ a = a ⊓ ⊤`. -/
theorem meet_self_eq_meet_top (a : τ) : (a ⊓ a) = (a ⊓ top) := by
  rw [meet_idem, meet_top]

/-- Base case at a negative literal: `∼a ⊓ a = ∼a ⊓ ⊥`. -/
theorem compl_meet_eq_meet_bot (a : τ) : ((∼ a) ⊓ a) = ((∼ a) ⊓ bot) := by
  rw [compl_meet_self, meet_bot]


end BA

end Classicism.Strict
