import Classicism.Syntax.Entailment

/-!
# Denotation, and soundness

The bridge between the metalogical layer and the other two: a **denotation** reading each
object-language type as a Lean type and each term as a Lean value, so that a sentence
denotes a proposition. It is parametrized by an interpretation of `e` and of the
signature's constants; with `t` read as `Prop`, the result is the **full Henkin model** of
the paper (Classicism, §3.2), and with `e` read as `ℕ` it is the model behind the map's
`full-henkin-infinite-base`.

The statement `⟦⌜p⌝⟧ = p`, that quoting a shallow statement and reading it back gives the
same proposition, is what the translator's quotations will be checked against, by `rfl`.

Then **soundness**: every rule of `Derivable` preserves truth in the model, so a theorem of
an axiom set true in the model is true in the model. The eleven identities are true in
`Prop`, each by `propext` and `funext`, which are available here: this layer is ordinary
Lean, and what it proves is that Lean's `Prop` is a model of Classicism. Consequences: `C`
is consistent, and no sentence false in `Prop` is a theorem of it.
-/

namespace Classicism.Meta

/-! ### Types and contexts -/

mutual
  /-- The Lean type denoted by an object type, given the type `D` denoted by `e`. -/
  def Ty.denote (D : Type) : Ty → Type
    | .e => D
    | .rel ρ => ρ.denote D
    | .var _ => D
  /-- `t` is `Prop`, and an arrow is a function type. -/
  def RTy.denote (D : Type) : RTy → Type
    | .t => Prop
    | .arr σ ρ => σ.denote D → ρ.denote D
end

-- Reducible, so that `⟦t⟧` *is* `Prop` to instance search and to `simp`'s matching: the
-- reflection of a shallow statement rewrites `¬p ∨ q` to `p → q` under binders of type `⟦t⟧`.
attribute [reducible] Ty.denote RTy.denote

/-- An environment: a value for each variable of the context, innermost first. An
inductive family rather than nested pairs, so that its type is always literally
`Env D Γ`. -/
inductive Env (D : Type) : Ctx → Type
  /-- The empty environment. -/
  | nil : Env D []
  /-- A value for the innermost variable, and the rest. -/
  | cons {Γ : Ctx} {σ : Ty} : Ty.denote D σ → Env D Γ → Env D (σ :: Γ)

/-- An interpretation: what `e` denotes, and what each constant denotes. -/
structure Interp (Sig : Signature) where
  /-- The domain of `e`. -/
  D : Type
  /-- The value of each nonlogical constant. -/
  const : ∀ c : Sig.Const, Ty.denote D (Sig.typeOf c)

/-- The pure language needs only a domain. -/
def Interp.ofDomain (D : Type) : Interp Signature.pure := ⟨D, fun c => nomatch c⟩

variable {Sig : Signature}

/-- The value of a variable in an environment. -/
def Var.denote {D : Type} : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → Env D Γ → Ty.denote D σ
  | _, _, .zero, .cons x _ => x
  | _, _, .succ v, .cons _ env => v.denote env

/-! ### The type-subscripted operations, on the reading of a type

Each by recursion on the type, as the paper defines it; at `t` written out as the
reading of the unfolding, so that the δ-rule preserves denotation by `rfl`. That these
are the strict layer's `SRel` operations is `Relational.lean`. -/

section
variable (D : Type)
/-- `const_ρ`. -/
def RTy.constD : ∀ ρ : RTy, Prop → ρ.denote D
  | .t, p => p
  | .arr _ ρ, p => fun _ => constD ρ p
/-- `¬_ρ`. -/
def RTy.negD : ∀ ρ : RTy, ρ.denote D → ρ.denote D
  | .t, p => ¬ p
  | .arr _ ρ, X => fun z => negD ρ (X z)
/-- `∧_ρ`. -/
def RTy.andD : ∀ ρ : RTy, ρ.denote D → ρ.denote D → ρ.denote D
  | .t, p, q => p ∧ q
  | .arr _ ρ, X, Y => fun z => andD ρ (X z) (Y z)
/-- `∨_ρ`. -/
def RTy.orD : ∀ ρ : RTy, ρ.denote D → ρ.denote D → ρ.denote D
  | .t, p, q => p ∨ q
  | .arr _ ρ, X, Y => fun z => orD ρ (X z) (Y z)
/-- Coextensiveness at `ρ`; at `t`, `p ↔ q` as `(¬p ∨ q) ∧ (¬q ∨ p)`. -/
def RTy.coextD : ∀ ρ : RTy, ρ.denote D → ρ.denote D → Prop
  | .t, p, q => (¬ p ∨ q) ∧ (¬ q ∨ p)
  | .arr _ ρ, X, Y => ∀ z, coextD ρ (X z) (Y z)
/-- `□_ρ`; at `t`, `p = ⊤` with `⊤` read as the sentence `∀p. p ∨ ¬∀p. p` is. -/
def RTy.boxD : ∀ ρ : RTy, ρ.denote D → ρ.denote D
  | .t, p => p = ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q)
  | .arr _ ρ, X => fun z => boxD ρ (X z)
/-- Pointwise implication at `ρ`; at `t`, `¬p ∨ q`. -/
def RTy.inclD : ∀ ρ : RTy, ρ.denote D → ρ.denote D → Prop
  | .t, p, q => ¬ p ∨ q
  | .arr _ ρ, X, Y => ∀ z, inclD ρ (X z) (Y z)
end

/-! ### Terms -/

/-- The value of a term in an environment. The logical constants denote Lean's own
connectives, quantifiers and identity, and the type-subscripted operations the recursions
above. -/
def Term.denote (I : Interp Sig) :
    ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Env I.D Γ → Ty.denote I.D σ
  | _, _, .var v, env => v.denote env
  | _, _, .const c, _ => I.const c
  | _, _, .app f a, env => (f.denote I env) (a.denote I env)
  | _, _, .lam b, env => fun x => b.denote I (.cons x env)
  | _, _, .and, _ => fun p q => p ∧ q
  | _, _, .or, _ => fun p q => p ∨ q
  | _, _, .not, _ => fun p => ¬ p
  | _, _, .all _, _ => fun F => ∀ x, F x
  | _, _, .ex _, _ => fun F => ∃ x, F x
  | _, _, .eq _, _ => fun a b => a = b
  | _, _, .constR ρ, _ => RTy.constD I.D ρ
  | _, _, .negR ρ, _ => RTy.negD I.D ρ
  | _, _, .andR ρ, _ => RTy.andD I.D ρ
  | _, _, .orR ρ, _ => RTy.orD I.D ρ
  | _, _, .coextR ρ, _ => RTy.coextD I.D ρ
  | _, _, .boxR ρ, _ => RTy.boxD I.D ρ
  | _, _, .inclR ρ, _ => RTy.inclD I.D ρ

/-- A sentence holds in an interpretation. -/
abbrev Sentence.holds (I : Interp Sig) (p : Sentence Sig) : Prop := p.denote I .nil

/-- An axiom set holds in an interpretation. -/
def AxiomSet.holds (I : Interp Sig) (Ax : AxiomSet Sig) : Prop := ∀ a, Ax a → a.holds I

/-! ### Renaming and substitution commute with denotation

A renaming or substitution pulls an environment back along itself; the lemmas say the
value of a renamed or substituted term is the value of the term in the pulled-back
environment. -/

/-- The environment a renaming pulls back. -/
def Ren.denote {D : Type} : ∀ {Γ Δ : Ctx}, Ren Γ Δ → Env D Δ → Env D Γ
  | [], _, _, _ => .nil
  | _ :: _, _, r, env => .cons (Var.denote (r _ .zero) env) (Ren.denote (fun _ v => r _ (.succ v)) env)

theorem Var.denote_ren {D : Type} : ∀ {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (v : Var Γ σ)
    (env : Env D Δ), Var.denote v (Ren.denote r env) = Var.denote (r _ v) env
  | _, _, _, _, .zero, _ => rfl
  | _, _, _, r, .succ v, env => Var.denote_ren (fun _ v => r _ (.succ v)) v env

theorem Ren.denote_congr {D : Type} : ∀ {Γ Δ Δ' : Ctx} (r : Ren Γ Δ) (r' : Ren Γ Δ')
    (env : Env D Δ) (env' : Env D Δ'),
    (∀ σ (v : Var Γ σ), Var.denote (r _ v) env = Var.denote (r' _ v) env') →
    Ren.denote r env = Ren.denote r' env'
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, r, r', env, env', h => by
    simp only [Ren.denote]
    rw [h _ .zero, Ren.denote_congr _ _ env env' (fun _ v => h _ (.succ v))]

theorem Ren.denote_lift {D : Type} {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (x : Ty.denote D σ)
    (env : Env D Δ) :
    Ren.denote (Ren.lift r (σ := σ)) (.cons x env) = .cons x (Ren.denote r env) := by
  simp only [Ren.denote, Ren.lift, Var.denote]
  exact congrArg _ (Ren.denote_congr _ _ _ _ (fun _ _ => rfl))

theorem Ren.denote_shift {D : Type} : ∀ {Γ : Ctx} {σ : Ty} (x : Ty.denote D σ) (env : Env D Γ),
    Ren.denote (Ren.shift (σ := σ)) (.cons x env) = env
  | [], _, _, .nil => rfl
  | _ :: _, _, x, .cons y env => by
    simp only [Ren.denote, Ren.shift, Var.denote]
    rw [Ren.denote_congr (fun _ v => Var.succ (Var.succ v)) (Ren.shift) (.cons x (.cons y env))
      (.cons x env) (fun _ _ => rfl), Ren.denote_shift x env]

theorem Term.denote_rename (I : Interp Sig) :
    ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ) (env : Env I.D Δ),
      (a.rename r).denote I env = a.denote I (Ren.denote r env)
  | _, _, r, _, .var v, env => (Var.denote_ren r v env).symm
  | _, _, _, _, .const _, _ | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _
  | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _
  | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _ | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _
  | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl
  | _, _, r, _, .app f a, env => by
    simp only [Term.rename_app, Term.denote, Term.denote_rename I r f, Term.denote_rename I r a]
  | _, _, r, _, .lam b, env => by
    simp only [Term.rename_lam, Term.denote]
    funext x
    rw [Term.denote_rename I (Ren.lift r) b, Ren.denote_lift]

theorem Term.denote_weaken (I : Interp Sig) {Γ : Ctx} {σ τ : Ty} (a : Term Sig Γ σ)
    (x : Ty.denote I.D τ) (env : Env I.D Γ) :
    (a.weaken (τ := τ)).denote I (.cons x env) = a.denote I env := by
  rw [Term.weaken, Term.denote_rename, Ren.denote_shift]

/-- The same, for a formula, with the identity stated at `Prop` so that `rw` accepts it:
a rewrite needs a motive whose codomain is syntactically a sort, and `Ty.denote D t`
is `Prop` only after unfolding. -/
theorem Formula.denote_weaken (I : Interp Sig) {Γ : Ctx} {τ : Ty} (a : Formula Sig Γ)
    (x : Ty.denote I.D τ) (env : Env I.D Γ) :
    ((a.weaken (τ := τ)).denote I (.cons x env) : Prop) = a.denote I env :=
  Term.denote_weaken I a x env

/-- The environment a substitution pulls back. -/
def Sub.denote (I : Interp Sig) : ∀ {Γ Δ : Ctx}, Sub Sig Γ Δ → Env I.D Δ → Env I.D Γ
  | [], _, _, _ => .nil
  | _ :: _, _, s, env => .cons ((s _ .zero).denote I env) (Sub.denote I (fun _ v => s _ (.succ v)) env)

theorem Var.denote_sub (I : Interp Sig) : ∀ {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig Γ Δ) (v : Var Γ σ)
    (env : Env I.D Δ), Var.denote v (Sub.denote I s env) = (s _ v).denote I env
  | _, _, _, _, .zero, _ => rfl
  | _, _, _, s, .succ v, env => Var.denote_sub I (fun _ v => s _ (.succ v)) v env

theorem Sub.denote_congr (I : Interp Sig) : ∀ {Γ Δ Δ' : Ctx} (s : Sub Sig Γ Δ) (s' : Sub Sig Γ Δ')
    (env : Env I.D Δ) (env' : Env I.D Δ'),
    (∀ σ (v : Var Γ σ), (s _ v).denote I env = (s' _ v).denote I env') →
    Sub.denote I s env = Sub.denote I s' env'
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, s, s', env, env', h => by
    simp only [Sub.denote]
    rw [h _ .zero, Sub.denote_congr I _ _ env env' (fun _ v => h _ (.succ v))]

theorem Sub.denote_lift (I : Interp Sig) {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig Γ Δ)
    (x : Ty.denote I.D σ) (env : Env I.D Δ) :
    Sub.denote I (Sub.lift s (σ := σ)) (.cons x env) = .cons x (Sub.denote I s env) := by
  simp only [Sub.denote, Sub.lift, Term.denote, Var.denote]
  rw [Sub.denote_congr I _ _ _ _ (fun _ v => Term.denote_weaken I (s _ v) x env)]

theorem Sub.denote_id (I : Interp Sig) : ∀ {Γ : Ctx} (env : Env I.D Γ),
    Sub.denote I Sub.id env = env
  | [], .nil => rfl
  | _ :: _, .cons x env => by
    simp only [Sub.denote, Sub.id, Term.denote, Var.denote]
    rw [Sub.denote_congr I (fun _ v => Term.var (Var.succ v)) Sub.id (.cons x env) env
      (fun _ _ => rfl), Sub.denote_id I env]

theorem Term.denote_subst (I : Interp Sig) :
    ∀ {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {σ : Ty} (a : Term Sig Γ σ) (env : Env I.D Δ),
      (a.subst s).denote I env = a.denote I (Sub.denote I s env)
  | _, _, s, _, .var v, env => (Var.denote_sub I s v env).symm
  | _, _, _, _, .const _, _ | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _
  | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _
  | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _ | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _
  | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl
  | _, _, s, _, .app f a, env => by
    simp only [Term.subst_app, Term.denote, Term.denote_subst I s f, Term.denote_subst I s a]
  | _, _, s, _, .lam b, env => by
    simp only [Term.subst_lam, Term.denote]
    funext x
    rw [Term.denote_subst I (Sub.lift s) b, Sub.denote_lift]

theorem Term.denote_instantiate (I : Interp Sig) {Γ : Ctx} {σ τ : Ty} (b : Term Sig (σ :: Γ) τ)
    (a : Term Sig Γ σ) (env : Env I.D Γ) :
    (b.instantiate a).denote I env = b.denote I (.cons (a.denote I env) env) := by
  rw [Term.instantiate, Term.denote_subst]
  simp only [Sub.denote, Sub.cons]
  rw [Sub.denote_id]

theorem Term.denote_close (I : Interp Sig) {Γ : Ctx} {σ : Ty} (a : Term Sig [] σ)
    (env : Env I.D Γ) : a.close.denote I env = a.denote I .nil := by
  rw [Term.close, Term.denote_rename]; rfl

/-! ### Conversion preserves denotation -/

theorem Beta.denote (I : Interp Sig) {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ} (h : Beta a b)
    (env : Env I.D Γ) : a.denote I env = b.denote I env := by
  cases h with
  | intro b a =>
    show (fun x => b.denote I (.cons x env)) (a.denote I env) = _
    rw [Term.denote_instantiate]

theorem Eta.denote (I : Interp Sig) {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ} (h : Eta a b)
    (env : Env I.D Γ) : a.denote I env = b.denote I env := by
  cases h with
  | intro f =>
    show (fun x => (f.weaken.denote I (.cons x env)) (Var.denote Var.zero (.cons x env))) = _
    funext x; rw [Term.denote_weaken]; rfl

/-- The δ-rule preserves denotation: each unfolding reads as the recursion it unfolds,
by `rfl` at both shapes of type. -/
theorem Delta.denote (I : Interp Sig) : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, Delta a b →
    ∀ (env : Env I.D Γ), a.denote I env = b.denote I env
  | _, _, .constR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .negR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .andR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .orR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .coextR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .boxR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .inclR ρ, _, h, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .var _, _, h, _ | _, _, .const _, _, h, _ | _, _, .app _ _, _, h, _ | _, _, .lam _, _, h, _
  | _, _, .and, _, h, _ | _, _, .or, _, h, _ | _, _, .not, _, h, _ | _, _, .all _, _, h, _
  | _, _, .ex _, _, h, _ | _, _, .eq _, _, h, _ => nomatch h

theorem Step.denote (I : Interp Sig)
    {R : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Term Sig Γ σ → Prop}
    (hR : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, R a b →
      ∀ env : Env I.D Γ, a.denote I env = b.denote I env) :
    ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, Step R a b →
      ∀ env : Env I.D Γ, a.denote I env = b.denote I env
  | _, _, _, _, .here h, env => hR h env
  | _, _, _, _, .appL (f := f) (f' := f') (a := a) h, env => by
    show f.denote I env (a.denote I env) = f'.denote I env (a.denote I env)
    rw [Step.denote I hR h env]
  | _, _, _, _, .appR (f := f) (a := a) (a' := a') h, env => by
    show f.denote I env (a.denote I env) = f.denote I env (a'.denote I env)
    rw [Step.denote I hR h env]
  | _, _, _, _, .lam (b := b) (b' := b') h, env => by
    show (fun x => b.denote I (.cons x env)) = (fun x => b'.denote I (.cons x env))
    funext x; rw [Step.denote I hR h (.cons x env)]

theorem Conv.denote (I : Interp Sig) {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ} (h : a ≡ b)
    (env : Env I.D Γ) : a.denote I env = b.denote I env := by
  induction h with
  | rel h => exact Step.denote I (fun h env => h.elim (Beta.denote I · env)
      (fun h => h.elim (Eta.denote I · env) (Delta.denote I · env))) h env
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Soundness -/

/-- Every hypothesis holds in the environment. -/
def Hyps.holds (I : Interp Sig) {Γ : Ctx} (Δ : List (Formula Sig Γ)) (env : Env I.D Γ) : Prop :=
  ∀ q ∈ Δ, q.denote I env

theorem Hyps.holds_weaken (I : Interp Sig) {Γ : Ctx} {σ : Ty} (Δ : List (Formula Sig Γ))
    (x : Ty.denote I.D σ) (env : Env I.D Γ) (h : Hyps.holds I Δ env) :
    Hyps.holds I (Hyps.weaken (σ := σ) Δ) (.cons x env) := by
  intro q hq
  rw [Hyps.weaken, List.mem_map] at hq
  obtain ⟨q', hq', e⟩ := hq
  exact Eq.mp (congrArg (fun q => Term.denote I q (.cons x env)) e)
    (Eq.mpr (Formula.denote_weaken I q' x env) (h q' hq'))

/-- Filling a hole with terms of the same value gives terms of the same value. -/
theorem Hole.plug_denote_congr (I : Interp Sig) : ∀ {Γ Γ' : Ctx} {σ τ : Ty} (K : Hole Sig Γ σ Γ' τ)
    {a b : Term Sig Γ' τ}, (∀ env', a.denote I env' = b.denote I env') →
    ∀ env : Env I.D Γ, (K.plug a).denote I env = (K.plug b).denote I env
  | _, _, _, _, .hole, _, _, e, env => e env
  | _, _, _, _, .appL K c, a, b, e, env => by
    show (K.plug a).denote I env (c.denote I env) = (K.plug b).denote I env (c.denote I env)
    rw [plug_denote_congr I K e env]
  | _, _, _, _, .appR f K, a, b, e, env => by
    show f.denote I env ((K.plug a).denote I env) = f.denote I env ((K.plug b).denote I env)
    rw [plug_denote_congr I K e env]
  | _, _, _, _, .lam K, a, b, e, env => by
    show (fun x => (K.plug a).denote I (.cons x env)) = (fun x => (K.plug b).denote I (.cons x env))
    funext x
    exact plug_denote_congr I K e (.cons x env)

/-- **Soundness.** A derivation from hypotheses true in an environment, in a theory whose
axioms hold in the interpretation, has a true conclusion. -/
theorem Derivable.sound (I : Interp Sig) :
    ∀ {Ax : AxiomSet Sig}, Ax.holds I →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}, Derivable Ax Δ p →
      ∀ env : Env I.D Γ, Hyps.holds I Δ env → p.denote I env
  | _, hAx, _, _, _, .hyp h, _, hΔ => hΔ _ h
  | _, hAx, _, _, _, .ax h, env, _ => by rw [Term.denote_close]; exact hAx _ h
  | _, hAx, _, _, _, .andI h₁ h₂, env, hΔ => ⟨sound I hAx h₁ env hΔ, sound I hAx h₂ env hΔ⟩
  | _, hAx, _, _, _, .andE₁ h, env, hΔ => (sound I hAx h env hΔ).1
  | _, hAx, _, _, _, .andE₂ h, env, hΔ => (sound I hAx h env hΔ).2
  | _, hAx, _, _, _, .orI₁ h, env, hΔ => Or.inl (sound I hAx h env hΔ)
  | _, hAx, _, _, _, .orI₂ h, env, hΔ => Or.inr (sound I hAx h env hΔ)
  | _, hAx, _, _, _, .orE h h₁ h₂, env, hΔ =>
    (sound I hAx h env hΔ).elim
      (fun hp => sound I hAx h₁ env (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hΔ q hq))
      (fun hq' => sound I hAx h₂ env (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hq'
        · exact hΔ q hq))
  | _, hAx, _, _, _, .notI h₁ h₂, env, hΔ => fun hp =>
    have hΔ' : Hyps.holds I (_ :: _) env := fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hΔ q hq
    sound I hAx h₂ env hΔ' (sound I hAx h₁ env hΔ')
  | _, hAx, _, _, _, .notE h₁ h₂, env, hΔ => absurd (sound I hAx h₁ env hΔ) (sound I hAx h₂ env hΔ)
  | _, hAx, _, _, _, .em p, env, _ => Classical.em (p.denote I env)
  | _, hAx, _, _, _, .allE h a, env, hΔ => sound I hAx h env hΔ (a.denote I env)
  | _, hAx, _, _, _, .allI h, env, hΔ => fun x => sound I hAx h (.cons x env) (Hyps.holds_weaken I _ x env hΔ)
  | _, hAx, _, _, _, .exI a h, env, hΔ => ⟨a.denote I env, sound I hAx h env hΔ⟩
  | _, hAx, _, _, _, .exE (F := F) (r := r) h h', env, hΔ => by
    obtain ⟨x, hx⟩ := sound I hAx h env hΔ
    have := sound I hAx h' (.cons x env) (fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · show F.weaken.denote I (.cons x env) (Var.denote Var.zero (.cons x env))
        exact Eq.mpr (congrFun (Term.denote_weaken I F x env) _) hx
      · exact Hyps.holds_weaken I _ x env hΔ q hq)
    exact Eq.mp (Formula.denote_weaken I r x env) this
  | _, hAx, _, _, _, .refl a, _, _ => rfl
  | _, hAx, _, _, _, .ll (a := a) (b := b) F h₁ h₂, env, hΔ => by
    have e : a.denote I env = b.denote I env := sound I hAx h₁ env hΔ
    have h : F.denote I env (a.denote I env) := sound I hAx h₂ env hΔ
    show F.denote I env (b.denote I env)
    rw [← e]; exact h
  | _, hAx, _, _, _, .conv h c, env, hΔ => by
    rw [← Conv.denote I c env]; exact sound I hAx h env hΔ
  | Ax, hAx, _, _, _, .subst (P := P) (Q := Q) K h₁ h₂ h₃, env, hΔ => by
    have hL : AxiomSet.holds I Ax.logical := fun a ha => hAx a ha.1
    have e : ∀ env', P.denote I env' = Q.denote I env' := fun env' => propext
      ⟨fun hp => sound I hL h₁ env' (fun q hq => by rw [List.mem_singleton.1 hq]; exact hp),
       fun hq => sound I hL h₂ env' (fun q hq' => by rw [List.mem_singleton.1 hq']; exact hq)⟩
    rw [← Hole.plug_denote_congr I K e env]
    exact sound I hAx h₃ env hΔ

/-- A theorem of a theory holds in every model of the theory. -/
theorem Theorem.holds (I : Interp Sig) {Ax : AxiomSet Sig} (hAx : Ax.holds I) {p : Sentence Sig}
    (h : Theorem Ax p) : p.holds I :=
  Derivable.sound I hAx h .nil (fun _ h => nomatch h)

/-- Entailment transfers holding: in a model of `C` and `Ax₁`, `Ax₂` holds too. -/
theorem AxiomSet.Entails.holds (I : Interp Sig) (hC : C.axioms.holds I) {Ax₁ Ax₂ : AxiomSet Sig}
    (e : Ax₁ ⟹ Ax₂) (h₁ : Ax₁.holds I) : Ax₂.holds I :=
  fun a ha => Theorem.holds I (fun b hb => hb.elim (hC b) (h₁ b)) (e a ha)

/-! ### `Prop` is a model of Classicism

Existence at `e` needs the domain inhabited; that is all `C.axioms` asks. The eleven
identities are true in `Prop` too: the two sides denote functions that agree at every
argument by a propositional or quantifier equivalence, so `propext` and `funext` identify
them. That they are theorems of `C` makes this a corollary of soundness; it is kept as a
direct check. -/

namespace C

theorem identities_holds (I : Interp Sig) : C.identities.holds I := by
  intro a h
  cases h with
  | commutativity_and =>
    show (fun p q : Prop => p ∧ q) = (fun p q => q ∧ p)
    funext p q; exact propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩
  | commutativity_or =>
    show (fun p q : Prop => p ∨ q) = (fun p q => q ∨ p)
    funext p q; exact propext ⟨Or.symm, Or.symm⟩
  | distribution_and_or =>
    show (fun p q r : Prop => p ∧ (q ∨ r)) = (fun p q r => (p ∧ q) ∨ (p ∧ r))
    funext p q r; exact propext ⟨fun ⟨hp, hqr⟩ => hqr.elim (fun h => Or.inl ⟨hp, h⟩) (fun h => Or.inr ⟨hp, h⟩),
      fun h => h.elim (fun ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩) (fun ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩)⟩
  | distribution_or_and =>
    show (fun p q r : Prop => p ∨ (q ∧ r)) = (fun p q r => (p ∨ q) ∧ (p ∨ r))
    funext p q r; exact propext ⟨fun h => h.elim (fun hp => ⟨Or.inl hp, Or.inl hp⟩) (fun ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩),
      fun ⟨h₁, h₂⟩ => h₁.elim Or.inl (fun hq => h₂.elim Or.inl (fun hr => Or.inr ⟨hq, hr⟩))⟩
  | dissolution_and_or =>
    show (fun p q : Prop => p ∧ (q ∨ ¬ q)) = (fun p _ => p)
    funext p q; exact propext ⟨And.left, fun hp => ⟨hp, Classical.em q⟩⟩
  | dissolution_or_and =>
    show (fun p q : Prop => p ∨ (q ∧ ¬ q)) = (fun p _ => p)
    funext p q; exact propext ⟨fun h => h.elim id (fun ⟨h₁, h₂⟩ => absurd h₁ h₂), Or.inl⟩
  | identity_identity σ =>
    show (fun y z : σ.denote I.D => y = z) = (fun y z => ∀ X : σ.denote I.D → Prop, (¬ X y ∨ X z) ∧ (¬ X z ∨ X y))
    funext y z; exact propext ⟨fun h => h ▸ fun X => ⟨Classical.em (X y) |>.symm, Classical.em (X y) |>.symm⟩,
      fun h => ((h (fun w => y = w)).1).elim (fun hn => absurd rfl hn) id⟩
  | absorption_or_forall σ =>
    show (fun (X : σ.denote I.D → Prop) y => X y ∨ ∀ x, X x) = (fun X y => X y)
    funext X y; exact propext ⟨fun h => h.elim id (fun h => h y), Or.inl⟩
  | distribution_or_forall σ =>
    show (fun (X : σ.denote I.D → Prop) (p : Prop) => p ∨ ∀ x, X x) = (fun X p => ∀ y, p ∨ X y)
    funext X p; exact propext ⟨fun h y => h.elim Or.inl (fun h => Or.inr (h y)),
      fun h => (Classical.em p).elim Or.inl (fun hn => Or.inr fun y => (h y).elim (fun hp => absurd hp hn) id)⟩
  | absorption_and_exists σ =>
    show (fun (X : σ.denote I.D → Prop) y => X y ∧ ∃ x, X x) = (fun X y => X y)
    funext X y; exact propext ⟨And.left, fun h => ⟨h, y, h⟩⟩
  | distribution_and_exists σ =>
    show (fun (X : σ.denote I.D → Prop) (p : Prop) => p ∧ ∃ x, X x) = (fun X p => ∃ y, p ∧ X y)
    funext X p; exact propext ⟨fun ⟨hp, x, hx⟩ => ⟨x, hp, hx⟩, fun ⟨x, hp, hx⟩ => ⟨hp, x, hx⟩⟩

theorem axioms_holds (I : Interp Sig) [Nonempty I.D] : C.axioms.holds I := by
  intro a h
  rw [show a = existence_e from h]
  show ∃ x : I.D, x = x
  exact ⟨Classical.ofNonempty, rfl⟩

/-- A theorem of `C` holds in `Prop`, for any inhabited domain; a theorem of `C⁻`, for any
domain. -/
theorem Theorem.holds (I : Interp Sig) [Nonempty I.D] {p : Sentence Sig} (h : C.Theorem p) :
    p.holds I :=
  Meta.Theorem.holds I (axioms_holds I) h

theorem TheoremMinus.holds (I : Interp Sig) {p : Sentence Sig} (h : C.TheoremMinus p) :
    p.holds I :=
  Meta.Theorem.holds I (fun _ h => h.elim) h

/-- **Classicism is consistent**: `⊥` is not a theorem. -/
theorem consistent : ¬ C.Theorem (Sig := Signature.pure) Term.bot := fun h =>
  have : Sentence.holds (Interp.ofDomain Unit) Term.bot :=
    @Theorem.holds _ (Interp.ofDomain Unit) ⟨()⟩ _ h
  this.2 this.1

end C

/-- **An axiom set true in `Prop` is consistent** with Classicism: the model refutes `⊥`.
The consistency facts that the side conditions of Possibility and Distinctness ask for
come from here when the full Henkin model gives them. -/
theorem AxiomSet.Consistent.of_interp (I : Interp Sig) [Nonempty I.D] {Ax : AxiomSet Sig}
    (h : Ax.holds I) : Ax.Consistent := fun hb =>
  have : Sentence.holds I Term.bot :=
    Meta.Theorem.holds I (fun a ha => ha.elim (C.axioms_holds I a) (h a)) hb
  this.2 this.1

/-- A sentence false in `Prop` is not a theorem of `C` with an axiom set true there. -/
theorem not_theorem_of_interp (I : Interp Sig) [Nonempty I.D] {Ax : AxiomSet Sig}
    (h : Ax.holds I) {p : Sentence Sig} (hp : ¬ p.holds I) : ¬ Theorem (C.axioms ∪ Ax) p :=
  fun hd => hp (Meta.Theorem.holds I (fun a ha => ha.elim (C.axioms_holds I a) (h a)) hd)

/-- Every object type is inhabited once `e` is: a default element, by recursion. -/
theorem Ty.denote_nonempty (D : Type) [Nonempty D] : ∀ σ : Ty, Nonempty (Ty.denote D σ)
  | .e => inferInstance
  | .var _ => inferInstance
  | .rel ρ => RTy.induction (motive := fun ρ => Nonempty (RTy.denote D ρ)) ⟨True⟩
      (fun _ _ ⟨x⟩ => ⟨fun _ => x⟩) ρ

/-- An interpretation of any signature over a nonempty domain: each constant denotes
some element of its type. -/
noncomputable def Interp.trivial (Sig : Signature) (D : Type) [Nonempty D] : Interp Sig :=
  ⟨D, fun c => Classical.choice (Ty.denote_nonempty D (Sig.typeOf c))⟩

instance (Sig : Signature) (D : Type) [Nonempty D] : Nonempty (Interp.trivial Sig D).D :=
  inferInstanceAs (Nonempty D)

end Classicism.Meta
