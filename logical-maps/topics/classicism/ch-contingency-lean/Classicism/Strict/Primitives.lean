import Classicism.Strict.Rules

/-!
# The base cases: every primitive proof constant is identical to `⊤`

Appendix A's base cases show each axiom of `H` identical to `⊤`. A Lean proof term has no
axiom schemes; it has *constants*, `And.intro`, `Or.elim`, `Eq.refl` and so on, each of
whose types is a closed formula. The base case for a constant `c : S` is therefore one
theorem, `S = ⊤`, called its **necessitation** here and stored under `Nec`. The transformer
handles every use of `c` the same way: cite `S = ⊤`, then feed it its arguments by the
general rules for `∀`-elimination and modus ponens. No constant needs code of its own.

Three kinds.

* **Propositional constants** (`And.intro`, `Or.elim`, `absurd`, …). Their types quantify
  over propositions only, so `S = ⊤` is a tautology under `∀`s: `boolean_eq` between
  λ-terms, then Proposition A.1 once per quantifier.
* **Identity**: `Ref` and `LL`, cases (iv) and (v), from the Identity Identity.
* **Quantifiers**: `Exists.intro` is case (iii). `∀`-introduction and elimination are rules,
  not constants, and live in the transformer.

Lean's recursors take a *motive*, which is not an object of any `R`-type. `Prim` restates
the few that occur with the motive instantiated, so that their types are formulas.
-/

namespace Classicism.Strict

open Classicism.Axiomatic BA

/-! ### Closing a λ-level identity under `∀`

Proposition A.1, `∀x.⊤ = ⊤`, once per bound variable. -/

theorem forall_top₁ {σ : Type} [Ty σ] {F : σ → Prop} (h : F = fun _ => Top) :
    (∀ x, F x) = Top :=
  (congrArg (fun K : σ → Prop => ∀ x, K x) h).trans forall_const_top

theorem forall_top₂ {σ ρ : Type} [Ty σ] [Ty ρ] {F : σ → ρ → Prop}
    (h : F = fun _ _ => Top) : (∀ x y, F x y) = Top :=
  forall_top₁ ((congrArg (fun (K : σ → ρ → Prop) x => ∀ y, K x y) h).trans
    (congrArg (fun (r : Prop) (_ : σ) => r) forall_const_top))

theorem forall_top₃ {σ ρ π : Type} [Ty σ] [Ty ρ] [Ty π] {F : σ → ρ → π → Prop}
    (h : F = fun _ _ _ => Top) : (∀ x y z, F x y z) = Top :=
  forall_top₂ ((congrArg (fun (K : σ → ρ → π → Prop) x y => ∀ z, K x y z) h).trans
    (congrArg (fun (r : Prop) (_ : σ) (_ : ρ) => r) forall_const_top))

/-- `⊤` holds. Intuitionistically: its second disjunct is provable. -/
theorem top_intro : Top := Or.inr (fun h => h False)

/-- From `p = ⊤` to `p`: how a necessitation yields the theorem itself. -/
theorem of_eq_top {p : Prop} (h : p = Top) : p := h ▸ top_intro

/-! ### Entailment from absorption, in any algebra -/

theorem BA.imp_top_of_join {τ : Type} [BA τ] {A B : τ} (h : (B ⊔ A) = B) : imp A B = top :=
  have key : imp A (B ⊔ A) = top := by boolean_eq
  by rw [h] at key; exact key

theorem BA.imp_top_of_meet {τ : Type} [BA τ] {A B : τ} (h : (A ⊓ B) = A) : imp A B = top :=
  have key : imp (A ⊓ B) B = top := by boolean_eq
  by rw [h] at key; exact key

/-! ### `Ref` and `LL`, λ-closed

Cases (iv) and (v). Both come from the Identity Identity, `y = z` being `∀X. Xy ↔ Xz`. -/

/-- `Ref`: `(λy. y = y) = (λy. ⊤)`. -/
theorem ref_lam (σ : Type) [Ty σ] : (fun y : σ => y = y) = (fun _ => Top) :=
  have h : (fun (y : σ) (X : σ → Prop) => Classicism.iff (X y) (X y)) = (fun _ _ => Top) := by
    boolean_eq
  calc (fun y : σ => y = y)
      = (fun y => ∀ X : σ → Prop, Classicism.iff (X y) (X y)) :=
        congrArg (fun (K : σ → σ → Prop) y => K y y) (identity_identity σ)
    _ = (fun _ => ∀ _ : σ → Prop, Top) :=
        congrArg (fun (K : σ → (σ → Prop) → Prop) y => ∀ X, K y X) h
    _ = (fun _ => Top) := congrArg (fun (r : Prop) (_ : σ) => r) forall_const_top

/-- `LL`: `(λabP. a = b → Pa → Pb) = (λabP. ⊤)`. Rewrite `a = b` by the Identity Identity,
instantiate the quantifier at `P` by Absorption-∨∀, and the rest is Boolean. -/
theorem ll_lam (σ : Type) [Ty σ] :
    (fun (a b : σ) (P : σ → Prop) => imp (a = b) (imp (P a) (P b))) = (fun _ _ _ => Top) :=
  let ALL : σ → σ → (σ → Prop) → Prop := fun a b _ => ∀ X : σ → Prop, Classicism.iff (X a) (X b)
  let INST : σ → σ → (σ → Prop) → Prop := fun a b P => Classicism.iff (P a) (P b)
  have eq_all : (fun (a b : σ) (_ : σ → Prop) => a = b) = ALL :=
    congrArg (fun (K : σ → σ → Prop) a b (_ : σ → Prop) => K a b) (identity_identity σ)
  have ui : BA.or INST ALL = INST :=
    congrArg (fun (K : ((σ → Prop) → Prop) → (σ → Prop) → Prop) a b P =>
      K (fun X => Classicism.iff (X a) (X b)) P) (absorption_or_forall (σ → Prop))
  have h₁ : BA.imp ALL INST = BA.top := BA.imp_top_of_join ui
  have taut : BA.imp (BA.imp ALL INST)
      (BA.imp ALL (fun a b P => imp (P a) (P b))) = BA.top := by boolean_eq
  have h₂ : BA.imp ALL (fun a b P => imp (P a) (P b)) = BA.top := BA.mp_top taut h₁
  calc (fun (a b : σ) (P : σ → Prop) => imp (a = b) (imp (P a) (P b)))
      = BA.imp ALL (fun a b P => imp (P a) (P b)) :=
        congrArg (fun (E : σ → σ → (σ → Prop) → Prop) =>
          BA.imp E (fun a b P => imp (P a) (P b))) eq_all
    _ = (fun _ _ _ => Top) := h₂

/-! ### `Prim`: recursors with their motives instantiated -/

namespace Prim

/-- Leibniz's Law, which is what `Eq.rec` is once its motive is a property. -/
theorem ll {σ : Type} [Ty σ] (a b : σ) (P : σ → Prop) (h : a = b) (m : P a) : P b := h ▸ m

/-! The identity lemmas of core Lean, each one Leibniz's Law at a particular property.
Their necessitations are not proved by hand: the transformer makes them, from these
proofs, like those of any other theorem. -/

theorem eq_symm {σ : Type} [Ty σ] {a b : σ} (h : a = b) : b = a :=
  ll a b (fun z => z = a) h (Eq.refl a)
theorem eq_trans {σ : Type} [Ty σ] {a b c : σ} (h₁ : a = b) (h₂ : b = c) : a = c :=
  ll b c (fun z => a = z) h₂ h₁
theorem eq_subst {σ : Type} [Ty σ] {motive : σ → Prop} {a b : σ} (h₁ : a = b)
    (h₂ : motive a) : motive b := ll a b motive h₁ h₂
theorem eq_mp {α β : Prop} (h : α = β) (a : α) : β := ll α β (fun z => z) h a
theorem eq_mpr {α β : Prop} (h : α = β) (b : β) : α := ll β α (fun z => z) (eq_symm h) b
theorem congr_arg {σ ρ : Type} [Ty σ] [RelTy ρ] {a₁ a₂ : σ} (f : σ → ρ) (h : a₁ = a₂) :
    f a₁ = f a₂ := ll a₁ a₂ (fun z => f a₁ = f z) h (Eq.refl (f a₁))
theorem congr_fun {σ ρ : Type} [Ty σ] [RelTy ρ] {f g : σ → ρ} (h : f = g) (a : σ) :
    f a = g a := ll f g (fun k => f a = k a) h (Eq.refl (f a))
theorem iff_of_eq {a b : Prop} (h : a = b) : a ↔ b :=
  ll a b (fun z => a ↔ z) h (Iff.intro (fun x => x) (fun x => x))

theorem and_rec {a b c : Prop} (f : a → b → c) (h : a ∧ b) : c := f h.1 h.2
theorem or_rec {a b c : Prop} (f : a → c) (g : b → c) (h : a ∨ b) : c := h.elim f g
theorem false_rec {c : Prop} (h : False) : c := h.elim
theorem exists_rec {σ : Type} [Ty σ] {p : σ → Prop} {c : Prop} (f : ∀ w, p w → c)
    (h : ∃ x, p x) : c := h.elim f

end Prim

/-! ### The table

`Nec.c` is the necessitation of the constant `c`. Its statement is `c`'s type, with type
arguments as parameters, read in the paper's vocabulary: `True ↦ ⊤`, `False ↦ ⊥`,
`→ ↦ imp`, `↔ ↦ iff`. The transformer checks that reading against each lemma when it cites
it, so a slip here is caught, not trusted. -/

namespace Nec

/-- Close a propositional tautology under its quantifiers. -/
macro "nec_taut₁" : tactic => `(tactic| (apply forall_top₁; boolean_eq))
@[inherit_doc «tacticNec_taut₁»]
macro "nec_taut₂" : tactic => `(tactic| (apply forall_top₂; boolean_eq))
@[inherit_doc «tacticNec_taut₁»]
macro "nec_taut₃" : tactic => `(tactic| (apply forall_top₃; boolean_eq))

theorem «And.intro» : (∀ a b : Prop, imp a (imp b (a ∧ b))) = Top := by nec_taut₂
theorem «And.left» : (∀ a b : Prop, imp (a ∧ b) a) = Top := by nec_taut₂
theorem «And.right» : (∀ a b : Prop, imp (a ∧ b) b) = Top := by nec_taut₂
theorem «Or.inl» : (∀ a b : Prop, imp a (a ∨ b)) = Top := by nec_taut₂
theorem «Or.inr» : (∀ a b : Prop, imp b (a ∨ b)) = Top := by nec_taut₂
theorem «Or.elim» : (∀ a b c : Prop, imp (a ∨ b) (imp (imp a c) (imp (imp b c) c))) = Top := by
  nec_taut₃
theorem «Iff.intro» :
    (∀ a b : Prop, imp (imp a b) (imp (imp b a) (Classicism.iff a b))) = Top := by nec_taut₂
theorem «Iff.mp» : (∀ a b : Prop, imp (Classicism.iff a b) (imp a b)) = Top := by nec_taut₂
theorem «Iff.mpr» : (∀ a b : Prop, imp (Classicism.iff a b) (imp b a)) = Top := by nec_taut₂
theorem «Iff.symm» : (∀ a b : Prop, imp (Classicism.iff a b) (Classicism.iff b a)) = Top := by
  nec_taut₂
theorem «Iff.refl» : (∀ a : Prop, Classicism.iff a a) = Top := by nec_taut₁
theorem «Iff.rfl» : (∀ a : Prop, Classicism.iff a a) = Top := by nec_taut₁
theorem «False.elim» : (∀ c : Prop, imp Bot c) = Top := by nec_taut₁
theorem «absurd» : (∀ a b : Prop, imp a (imp (¬ a) b)) = Top := by nec_taut₂
theorem «id» : (∀ a : Prop, imp a a) = Top := by nec_taut₁
theorem «trivial» : Top = Top := rfl
theorem «True.intro» : Top = Top := rfl
theorem «Classicism.em» : (∀ p : Prop, p ∨ ¬ p) = Top := by nec_taut₁

theorem «Classicism.Strict.Prim.and_rec» :
    (∀ a b c : Prop, imp (imp a (imp b c)) (imp (a ∧ b) c)) = Top := by nec_taut₃
theorem «Classicism.Strict.Prim.or_rec» :
    (∀ a b c : Prop, imp (imp a c) (imp (imp b c) (imp (a ∨ b) c))) = Top := by nec_taut₃
theorem «Classicism.Strict.Prim.false_rec» : (∀ c : Prop, imp Bot c) = Top := by nec_taut₁

theorem «Eq.refl» (σ : Type) [Ty σ] : (∀ a : σ, a = a) = Top := forall_top₁ (ref_lam σ)

theorem «Classicism.Strict.Prim.ll» (σ : Type) [Ty σ] :
    (∀ (a b : σ) (P : σ → Prop), imp (a = b) (imp (P a) (P b))) = Top :=
  forall_top₃ (ll_lam σ)

/-- `EG`, case (iii): Absorption-∧∃ says `Xy` entails `∃X`. -/
theorem «Exists.intro» (σ : Type) [Ty σ] :
    (∀ (p : σ → Prop) (w : σ), imp (p w) (∃ x, p x)) = Top :=
  forall_top₂ (F := fun (p : σ → Prop) (w : σ) => imp (p w) (∃ x, p x))
    (BA.imp_top_of_meet (absorption_and_exists σ))

/-- In any algebra: if `P → C` absorbs `A`, then `A ⊓ P` is below `C`. -/
theorem _root_.Classicism.Strict.BA.meet_le_of_absorb {τ : Type} [BA τ] {A P C : τ}
    (h : (BA.imp P C ⊔ A) = BA.imp P C) : (A ⊓ P) = (C ⊓ (A ⊓ P)) :=
  have h₁ : BA.imp A (BA.imp P C) = top := BA.imp_top_of_join h
  have taut : BA.imp (BA.imp A (BA.imp P C)) (BA.iff (A ⊓ P) (C ⊓ (A ⊓ P))) = top := by boolean_eq
  BA.eq_of_iff_top (BA.mp_top taut h₁)

/-- `∃`-elimination, the rule `Inst` of inductive step (iii). With `A := ∀w. pw → c`:
`A ∧ ∃p = ∃y.(A ∧ py)` by Distribution-∧∃; under the `∃`, `A ∧ py` is below `c` by `UI`;
and Distribution-∧∃ again brings `c` back out, so `A ∧ ∃p` is below `c`. -/
theorem «Classicism.Strict.Prim.exists_rec» (σ : Type) [Ty σ] :
    (∀ (p : σ → Prop) (c : Prop), imp (∀ w, imp (p w) c) (imp (∃ x, p x) c)) = Top := by
  apply forall_top₂
  let A : (σ → Prop) → Prop → Prop := fun p c => ∀ w, imp (p w) c
  let E : (σ → Prop) → Prop → Prop := fun p _ => ∃ x, p x
  let C : (σ → Prop) → Prop → Prop := fun _ c => c
  let A' : (σ → Prop) → Prop → σ → Prop := fun p c _ => ∀ w, imp (p w) c
  let P' : (σ → Prop) → Prop → σ → Prop := fun p _ y => p y
  let C' : (σ → Prop) → Prop → σ → Prop := fun _ c _ => c
  have ui : (BA.imp P' C' ⊔ A') = BA.imp P' C' :=
    congrArg (fun (K : (σ → Prop) → σ → Prop) (p : σ → Prop) (c : Prop) y =>
      K (fun w => imp (p w) c) y) (absorption_or_forall σ)
  have under : (A' ⊓ P') = (C' ⊓ (A' ⊓ P')) := BA.meet_le_of_absorb ui
  have dist₁ : (A ⊓ E) = (fun p c => ∃ y, (∀ w, imp (p w) c) ∧ p y) :=
    congrArg (fun (K : (σ → Prop) → Prop → Prop) (p : σ → Prop) (c : Prop) =>
      K p (∀ w, imp (p w) c)) (distribution_and_exists σ)
  have lift : (fun (p : σ → Prop) (c : Prop) => ∃ y, (∀ w, imp (p w) c) ∧ p y)
      = (fun p c => ∃ y, c ∧ ((∀ w, imp (p w) c) ∧ p y)) :=
    congrArg (fun (K : (σ → Prop) → Prop → σ → Prop) p c => ∃ y, K p c y) under
  have dist₂ : (fun (p : σ → Prop) (c : Prop) => c ∧ ∃ y, (∀ w, imp (p w) c) ∧ p y)
      = (fun p c => ∃ y, c ∧ ((∀ w, imp (p w) c) ∧ p y)) :=
    congrArg (fun (K : (σ → Prop) → Prop → Prop) (p : σ → Prop) (c : Prop) =>
      K (fun y => (∀ w, imp (p w) c) ∧ p y) c) (distribution_and_exists σ)
  have below : (A ⊓ E) = (C ⊓ (A ⊓ E)) :=
    calc (A ⊓ E) = (fun p c => ∃ y, (∀ w, imp (p w) c) ∧ p y) := dist₁
      _ = (fun p c => ∃ y, c ∧ ((∀ w, imp (p w) c) ∧ p y)) := lift
      _ = (C ⊓ (fun p c => ∃ y, (∀ w, imp (p w) c) ∧ p y)) := dist₂.symm
      _ = (C ⊓ (A ⊓ E)) := congrArg (fun K => C ⊓ K) dist₁.symm
  have h₁ : BA.imp (A ⊓ E) C = top :=
    BA.imp_top_of_meet (((BA.meet_comm (A ⊓ E) C).trans below.symm))
  have taut : BA.imp (BA.imp (A ⊓ E) C) (BA.imp A (BA.imp E C)) = top := by boolean_eq
  exact BA.mp_top taut h₁

/-- Existence at `e`. `H` proves `∃x. x = x` from `UI` and `EG` because its variables always
denote; in Lean that is the axiom `e_exists`, used here once to have an individual to
instantiate `EG` at. The identity itself is `Ref` under `∃`, then `EG`. -/
theorem «Classicism.e_exists» : (∃ x : e, x = x) = Top :=
  have h₁ : (∃ x : e, x = x) = (∃ _ : e, Top) := congrArg (fun K : e → Prop => ∃ x, K x) (ref_lam e)
  have h₂ : (∃ _ : e, Top) = Top :=
    e_exists.elim fun a _ => BA.of_seq_top (eg_top (fun _ : e => Top) a)
  h₁.trans h₂

end Nec

end Classicism.Strict
