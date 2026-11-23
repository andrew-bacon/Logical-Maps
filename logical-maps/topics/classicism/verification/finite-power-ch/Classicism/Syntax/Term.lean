import Classicism.Syntax.Types

/-!
# Terms of the object language

The terms of Classicism's language `L(Sig)` over a signature `Sig` of nonlogical constants
(Classicism, §1.1), as an **intrinsically typed** syntax: `Term Sig Γ σ` is the type of terms
of type `σ` whose free variables are those of the context `Γ`, so that an ill-typed term
cannot be written down. Variables are de Bruijn indices into `Γ`, which makes
α-equivalence syntactic identity and leaves β and η as the only conversions.

The logical constants are the paper's: `∧`, `∨`, `¬`, and at each type `σ` the
quantifiers `∀σ`, `∃σ` and identity `=σ`. They are constants, so application and
abstraction are the only ways to build a term; the paper's abbreviations `→`, `↔`, `⊤`,
`⊥`, `□` follow in `Term.imp` and friends.

The two operations every later module rests on are renaming and substitution, each a map
on variables lifted through binders, with the four composition laws relating them. These
are the standard de Bruijn algebra; nothing in them is specific to Classicism.
-/

namespace Classicism.Meta

/-- A signature: a type of nonlogical constants, each with a type of `R`. -/
structure Signature where
  /-- The constants. -/
  Const : Type
  /-- The type of each constant. -/
  typeOf : Const → Ty

/-- The pure language, with no nonlogical constants. -/
def Signature.pure : Signature := ⟨Empty, Empty.elim⟩

/-- A context: the types of the variables in scope, innermost first. -/
abbrev Ctx := List Ty

/-- A variable: a de Bruijn index into the context, carrying its type. -/
inductive Var : Ctx → Ty → Type
  /-- The innermost variable. -/
  | zero {Γ : Ctx} {σ : Ty} : Var (σ :: Γ) σ
  /-- A variable from further out. -/
  | succ {Γ : Ctx} {σ τ : Ty} : Var Γ σ → Var (τ :: Γ) σ
  deriving DecidableEq

/-- Terms of `L(Sig)` in context `Γ`, at type `σ`. -/
inductive Term (Sig : Signature) : Ctx → Ty → Type
  /-- A variable. -/
  | var {Γ σ} : Var Γ σ → Term Sig Γ σ
  /-- A nonlogical constant of `Sig`. -/
  | const {Γ} (c : Sig.Const) : Term Sig Γ (Sig.typeOf c)
  /-- Application. -/
  | app {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig Γ (σ ⇒ ρ) → Term Sig Γ σ → Term Sig Γ ρ
  /-- Abstraction over the innermost variable. -/
  | lam {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig (σ :: Γ) ρ → Term Sig Γ (σ ⇒ ρ)
  /-- Conjunction, of type `t → t → t`. -/
  | and {Γ} : Term Sig Γ (RTy.t ⇒ RTy.t ⇒ RTy.t)
  /-- Disjunction. -/
  | or {Γ} : Term Sig Γ (RTy.t ⇒ RTy.t ⇒ RTy.t)
  /-- Negation. -/
  | not {Γ} : Term Sig Γ (RTy.t ⇒ RTy.t)
  /-- The universal quantifier at `σ`, of type `(σ → t) → t`. -/
  | all {Γ} (σ : Ty) : Term Sig Γ ((σ ⇒ RTy.t) ⇒ RTy.t)
  /-- The existential quantifier at `σ`. -/
  | ex {Γ} (σ : Ty) : Term Sig Γ ((σ ⇒ RTy.t) ⇒ RTy.t)
  /-- Identity at `σ`, of type `σ → σ → t`. -/
  | eq {Γ} (σ : Ty) : Term Sig Γ (σ ⇒ σ ⇒ RTy.t)
  -- The paper's type-subscripted operations (Classicism, §1.1): the constant relation
  -- `λz̄. p`, pointwise negation, conjunction and disjunction, coextensiveness, the
  -- pointwise box, and pointwise implication, at a relational type `ρ`. They are
  -- constants with an unfolding rule each, `Term.unfoldR`: at `t` the propositional
  -- operation, at `σ → ρ` the operation at `ρ` applied pointwise, the paper's definition
  -- by recursion on the type read as a δ-rule of conversion. Constants rather than
  -- functions defined by that recursion, so that at a type *parameter* they are nodes of
  -- the syntax, which renaming and substitution pass through and a derivation by
  -- induction on the type can mention.
  /-- `const_ρ : t → ρ`, the constant relation. -/
  | constR {Γ} (ρ : RTy) : Term Sig Γ (RTy.t ⇒ ρ)
  /-- `¬_ρ : ρ → ρ`. -/
  | negR {Γ} (ρ : RTy) : Term Sig Γ (ρ ⇒ ρ)
  /-- `∧_ρ : ρ → ρ → ρ`. -/
  | andR {Γ} (ρ : RTy) : Term Sig Γ (ρ ⇒ ρ ⇒ ρ)
  /-- `∨_ρ : ρ → ρ → ρ`. -/
  | orR {Γ} (ρ : RTy) : Term Sig Γ (ρ ⇒ ρ ⇒ ρ)
  /-- Coextensiveness at `ρ`, `ρ → ρ → t`. -/
  | coextR {Γ} (ρ : RTy) : Term Sig Γ (ρ ⇒ ρ ⇒ RTy.t)
  /-- The pointwise box `□_ρ : ρ → ρ`. -/
  | boxR {Γ} (ρ : RTy) : Term Sig Γ (ρ ⇒ ρ)
  /-- Pointwise implication at `ρ`, `ρ → ρ → t`. -/
  | inclR {Γ} (ρ : RTy) : Term Sig Γ (ρ ⇒ ρ ⇒ RTy.t)

/-- A formula: a term of type `t`. -/
abbrev Formula (Sig : Signature) (Γ : Ctx) : Type := Term Sig Γ RTy.t

/-- A sentence: a closed formula. -/
abbrev Sentence (Sig : Signature) : Type := Formula Sig []

namespace Term

variable {Sig : Signature} {Γ : Ctx}

/-! ### The paper's abbreviations, Figure 1 -/

/-- `P ∧ Q`. -/
abbrev conj (p q : Formula Sig Γ) : Formula Sig Γ := .app (.app .and p) q
/-- `P ∨ Q`. -/
abbrev disj (p q : Formula Sig Γ) : Formula Sig Γ := .app (.app .or p) q
/-- `¬P`. -/
abbrev neg (p : Formula Sig Γ) : Formula Sig Γ := .app .not p
/-- `P → Q := ¬P ∨ Q`. -/
abbrev imp (p q : Formula Sig Γ) : Formula Sig Γ := disj (neg p) q
/-- `P ↔ Q := (P → Q) ∧ (Q → P)`. -/
abbrev iff (p q : Formula Sig Γ) : Formula Sig Γ := conj (imp p q) (imp q p)
/-- `∀v. P`, for `P` a formula with one more variable in scope: `∀σ (λv. P)`. -/
abbrev forall' {σ : Ty} (p : Formula Sig (σ :: Γ)) : Formula Sig Γ := .app (.all σ) (.lam p)
/-- `∃v. P`. -/
abbrev exists' {σ : Ty} (p : Formula Sig (σ :: Γ)) : Formula Sig Γ := .app (.ex σ) (.lam p)
/-- `A = B` at type `σ`. -/
abbrev eq' {σ : Ty} (a b : Term Sig Γ σ) : Formula Sig Γ := .app (.app (.eq σ) a) b
/-- `⊤ := ∀p.p ∨ ¬∀p.p`. -/
abbrev top : Formula Sig Γ :=
  disj (forall' (.var .zero)) (neg (forall' (.var .zero)))
/-- `⊥ := ∀p.p ∧ ¬∀p.p`. -/
abbrev bot : Formula Sig Γ :=
  conj (forall' (.var .zero)) (neg (forall' (.var .zero)))
/-- `□P := (P = ⊤)`. -/
abbrev box (p : Formula Sig Γ) : Formula Sig Γ := eq' p top
/-- `◇P := ¬(P = ⊥)`, as the map and the strict layer define it; that this is `¬□¬P` is
a theorem, `dia_eq_not_box_not`. -/
abbrev dia (p : Formula Sig Γ) : Formula Sig Γ := neg (eq' p bot)

/-- Short names for the three innermost variables. -/
abbrev v0 {Γ : Ctx} {σ : Ty} : Term Sig (σ :: Γ) σ := .var .zero
@[inherit_doc v0] abbrev v1 {Γ : Ctx} {σ τ : Ty} : Term Sig (τ :: σ :: Γ) σ := .var (.succ .zero)
@[inherit_doc v0] abbrev v2 {Γ : Ctx} {σ τ υ : Ty} : Term Sig (υ :: τ :: σ :: Γ) σ :=
  .var (.succ (.succ .zero))

/-- `⊤_ρ`. -/
abbrev topR (ρ : RTy) : Term Sig Γ ρ := .app (.constR ρ) top
/-- `⊥_ρ`. -/
abbrev botR (ρ : RTy) : Term Sig Γ ρ := .app (.constR ρ) bot
/-- `X ≤_ρ Y`, the algebraic order: `Y = X ∨_ρ Y`. -/
abbrev leR (ρ : RTy) (X Y : Term Sig Γ ρ) : Formula Sig Γ := eq' Y (.app (.app (.orR ρ) X) Y)

/-! ### The unfolding of the type-subscripted operations

One step of the paper's recursive definition, at a constructor type. At a type parameter
there is nothing to unfold, and the constant stands. -/

/-- `const_t` is `λp. p`; `const_{σ→ρ}` is `λp z. const_ρ p`. -/
def unfoldConst : ∀ (ρ : RTy), Option (Term Sig Γ (RTy.t ⇒ ρ))
  | .t => some (.lam v0)
  | .arr _ ρ => some (.lam (.lam (.app (.constR ρ) v1)))
/-- `¬_t` is `¬`; `¬_{σ→ρ}` is `λX z. ¬_ρ (X z)`. -/
def unfoldNeg : ∀ (ρ : RTy), Option (Term Sig Γ (ρ ⇒ ρ))
  | .t => some .not
  | .arr _ ρ => some (.lam (.lam (.app (.negR ρ) (.app v1 v0))))
/-- `∧_t` is `∧`; `∧_{σ→ρ}` is `λX Y z. X z ∧_ρ Y z`. -/
def unfoldAnd : ∀ (ρ : RTy), Option (Term Sig Γ (ρ ⇒ ρ ⇒ ρ))
  | .t => some .and
  | .arr _ ρ => some (.lam (.lam (.lam (.app (.app (.andR ρ) (.app v2 v0)) (.app v1 v0)))))
/-- `∨_t` is `∨`; `∨_{σ→ρ}` is `λX Y z. X z ∨_ρ Y z`. -/
def unfoldOr : ∀ (ρ : RTy), Option (Term Sig Γ (ρ ⇒ ρ ⇒ ρ))
  | .t => some .or
  | .arr _ ρ => some (.lam (.lam (.lam (.app (.app (.orR ρ) (.app v2 v0)) (.app v1 v0)))))
/-- Coextensiveness at `t` is `λp q. p ↔ q`; at `σ → ρ`, `λX Y. ∀z. X z ≡_ρ Y z`. -/
def unfoldCoext : ∀ (ρ : RTy), Option (Term Sig Γ (ρ ⇒ ρ ⇒ RTy.t))
  | .t => some (.lam (.lam (iff v1 v0)))
  | .arr _ ρ => some (.lam (.lam (forall' (.app (.app (.coextR ρ) (.app v2 v0)) (.app v1 v0)))))
/-- `□_t` is `λp. □p`; `□_{σ→ρ}` is `λX z. □_ρ (X z)`. -/
def unfoldBox : ∀ (ρ : RTy), Option (Term Sig Γ (ρ ⇒ ρ))
  | .t => some (.lam (box v0))
  | .arr _ ρ => some (.lam (.lam (.app (.boxR ρ) (.app v1 v0))))
/-- Pointwise implication at `t` is `λp q. p → q`; at `σ → ρ`, `λX Y. ∀z. X z ⊑_ρ Y z`. -/
def unfoldIncl : ∀ (ρ : RTy), Option (Term Sig Γ (ρ ⇒ ρ ⇒ RTy.t))
  | .t => some (.lam (.lam (imp v1 v0)))
  | .arr _ ρ => some (.lam (.lam (forall' (.app (.app (.inclR ρ) (.app v2 v0)) (.app v1 v0)))))

/-- The unfolding of a term that is a type-subscripted operation at a constructor type;
`none` for every other term, and stuck at a type parameter. -/
def unfoldR : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Option (Term Sig Γ σ)
  | _, _, .constR ρ => unfoldConst ρ
  | _, _, .negR ρ => unfoldNeg ρ
  | _, _, .andR ρ => unfoldAnd ρ
  | _, _, .orR ρ => unfoldOr ρ
  | _, _, .coextR ρ => unfoldCoext ρ
  | _, _, .boxR ρ => unfoldBox ρ
  | _, _, .inclR ρ => unfoldIncl ρ
  | _, _, _ => none

/-! ### Purity

A term is pure when it contains no nonlogical constant. Over the pure signature every
term is; over another, this is the side condition of No Pure Contingency and of the
Maximalist principles. -/

/-- Does the term contain no nonlogical constant? -/
def pure : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Bool
  | _, _, .var _ => true
  | _, _, .const _ => false
  | _, _, .app f a => f.pure && a.pure
  | _, _, .lam b => b.pure
  | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => true
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .inclR _ => true

/-! ### Closed types

A term is in the **paper's language** when every type occurring in it is closed: the type of
each of its subterms, which covers the type of every bound variable, of every argument, and
the type subscript of every logical constant. Type variables are a device of the metalogic
(`Syntax/Types.lean`); the map's sentence schemas range over the sentences of the paper's
language, so each requires this of its instances (`Syntax/SentenceSchemas.lean`). -/

/-- Is every type occurring in the term closed? Each constructor checks the types it
introduces: a variable its type, a constant its type, an abstraction its binder, a logical
constant its subscript. By induction, the type of every subterm is then closed
(`closed_of_closedTypes`). -/
def closedTypes : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Bool
  | _, σ, .var _ => decide σ.Closed
  | _, _, .const c => decide (Sig.typeOf c).Closed
  | _, _, .app f a => f.closedTypes && a.closedTypes
  | _, _, .lam (σ := σ) b => decide σ.Closed && b.closedTypes
  | _, _, .and | _, _, .or | _, _, .not => true
  | _, _, .all σ | _, _, .ex σ | _, _, .eq σ => decide σ.Closed
  | _, _, .constR ρ | _, _, .negR ρ | _, _, .andR ρ | _, _, .orR ρ | _, _, .coextR ρ
  | _, _, .boxR ρ | _, _, .inclR ρ => decide ρ.Closed

/-- The type of a term in the paper's language is closed. -/
theorem closed_of_closedTypes : ∀ {Γ : Ctx} {σ : Ty} {t : Term Sig Γ σ},
    t.closedTypes = true → σ.Closed
  | _, _, .var _, h | _, _, .const _, h => by simpa [closedTypes] using h
  | _, _, .app f _, h => by
    simp only [closedTypes, Bool.and_eq_true] at h; exact (closed_of_closedTypes h.1).2
  | _, _, .lam b, h => by
    simp only [closedTypes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, closed_of_closedTypes h.2⟩
  | _, _, .and, _ | _, _, .or, _ | _, _, .not, _ => by simp
  | _, _, .all _, h | _, _, .ex _, h | _, _, .eq _, h => by
    simp only [closedTypes, decide_eq_true_eq] at h; simp [h]
  | _, _, .constR _, h | _, _, .negR _, h | _, _, .andR _, h | _, _, .orR _, h
  | _, _, .coextR _, h | _, _, .boxR _, h | _, _, .inclR _, h => by
    simp only [closedTypes, decide_eq_true_eq] at h; simp [h]

/-! ### Renaming -/

end Term

/-- A renaming: a type-preserving map of variables from one context to another. -/
def Ren (Γ Δ : Ctx) : Type := ∀ σ : Ty, Var Γ σ → Var Δ σ

namespace Ren

variable {Γ Δ Θ : Ctx}

/-- The identity renaming. -/
def id : Ren Γ Γ := fun _ v => v

/-- Composition. -/
def comp (r : Ren Δ Θ) (r' : Ren Γ Δ) : Ren Γ Θ := fun _ v => r _ (r' _ v)

/-- Push a renaming under a binder. -/
def lift (r : Ren Γ Δ) {σ : Ty} : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r _ v)

/-- The renaming that moves everything out past a new innermost variable. -/
def shift {σ : Ty} : Ren Γ (σ :: Γ) := fun _ v => .succ v

@[simp] theorem lift_zero (r : Ren Γ Δ) {σ : Ty} : Ren.lift r (σ := σ) _ .zero = .zero := rfl
@[simp] theorem lift_succ (r : Ren Γ Δ) {σ τ : Ty} (v : Var Γ σ) :
    Ren.lift r (σ := τ) _ (.succ v) = .succ (r _ v) := rfl

theorem lift_id {σ : Ty} : Ren.lift (Ren.id : Ren Γ Γ) (σ := σ) = Ren.id := by
  funext τ v; cases v <;> rfl

theorem lift_comp (r : Ren Δ Θ) (r' : Ren Γ Δ) {σ : Ty} :
    Ren.lift (Ren.comp r r') (σ := σ) = Ren.comp (Ren.lift r) (Ren.lift r') := by
  funext τ v; cases v <;> rfl

end Ren

namespace Term

variable {Sig : Signature}

/-- Apply a renaming to a term, by structural recursion: the implementation of `rename`. -/
def renameImpl : ∀ {Γ Δ : Ctx}, Ren Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Term Sig Δ σ
  | _, _, r, _, .var v => .var (r _ v)
  | _, _, _, _, .const c => .const c
  | _, _, r, _, .app f a => .app (renameImpl r f) (renameImpl r a)
  | _, _, r, _, .lam b => .lam (renameImpl (Ren.lift r) b)
  | _, _, _, _, .and => .and
  | _, _, _, _, .or => .or
  | _, _, _, _, .not => .not
  | _, _, _, _, .all σ => .all σ
  | _, _, _, _, .ex σ => .ex σ
  | _, _, _, _, .eq σ => .eq σ
  | _, _, _, _, .constR ρ => .constR ρ
  | _, _, _, _, .negR ρ => .negR ρ
  | _, _, _, _, .andR ρ => .andR ρ
  | _, _, _, _, .orR ρ => .orR ρ
  | _, _, _, _, .coextR ρ => .coextR ρ
  | _, _, _, _, .boxR ρ => .boxR ρ
  | _, _, _, _, .inclR ρ => .inclR ρ

/-- Apply a renaming to a term.

Written through `Term.rec` directly rather than by structural recursion, as are `subst`
and the normalizer's `prename` and `step`: the kernel evaluates such a definition about
ten times faster than one compiled through `brecOn`, and the translator's derivations
are checked by evaluating these. The equations `rename_var` … `rename_eq` below hold by
`rfl` and are the simp set; the structural `renameImpl` is what the compiler runs. -/
@[implemented_by renameImpl]
def rename : ∀ {Γ Δ : Ctx}, Ren Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Term Sig Δ σ :=
  fun {_ Δ} r {_} t =>
    Term.rec (motive := fun Γ σ _ => ∀ Δ : Ctx, Ren Γ Δ → Term Sig Δ σ)
      (var := fun v _ r => Term.var (r _ v))
      (const := fun c _ _ => Term.const c)
      (app := fun _ _ f a Δ' r => Term.app (f Δ' r) (a Δ' r))
      (lam := fun _ b _ r => Term.lam (b _ (Ren.lift r)))
      (and := fun _ _ => Term.and) (or := fun _ _ => Term.or) (not := fun _ _ => Term.not)
      (all := fun σ _ _ => Term.all σ) (ex := fun σ _ _ => Term.ex σ) (eq := fun σ _ _ => Term.eq σ)
      (constR := fun ρ _ _ => Term.constR ρ) (negR := fun ρ _ _ => Term.negR ρ)
      (andR := fun ρ _ _ => Term.andR ρ) (orR := fun ρ _ _ => Term.orR ρ)
      (coextR := fun ρ _ _ => Term.coextR ρ) (boxR := fun ρ _ _ => Term.boxR ρ)
      (inclR := fun ρ _ _ => Term.inclR ρ)
      t Δ r

section
variable {Γ Δ : Ctx} (r : Ren Γ Δ)
@[simp] theorem rename_var {σ : Ty} (v : Var Γ σ) : rename (Sig := Sig) r (.var v) = .var (r _ v) := rfl
@[simp] theorem rename_const (c : Sig.Const) : rename r (.const c) = .const c := rfl
@[simp] theorem rename_app {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    rename r (.app f a) = .app (rename r f) (rename r a) := rfl
@[simp] theorem rename_lam {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    rename r (.lam b) = .lam (rename (Ren.lift r) b) := rfl
@[simp] theorem rename_and : rename (Sig := Sig) r .and = .and := rfl
@[simp] theorem rename_or : rename (Sig := Sig) r .or = .or := rfl
@[simp] theorem rename_not : rename (Sig := Sig) r .not = .not := rfl
@[simp] theorem rename_all (σ : Ty) : rename (Sig := Sig) r (.all σ) = .all σ := rfl
@[simp] theorem rename_ex (σ : Ty) : rename (Sig := Sig) r (.ex σ) = .ex σ := rfl
@[simp] theorem rename_eq (σ : Ty) : rename (Sig := Sig) r (.eq σ) = .eq σ := rfl
@[simp] theorem rename_constR (ρ : RTy) : rename (Sig := Sig) r (.constR ρ) = .constR ρ := rfl
@[simp] theorem rename_negR (ρ : RTy) : rename (Sig := Sig) r (.negR ρ) = .negR ρ := rfl
@[simp] theorem rename_andR (ρ : RTy) : rename (Sig := Sig) r (.andR ρ) = .andR ρ := rfl
@[simp] theorem rename_orR (ρ : RTy) : rename (Sig := Sig) r (.orR ρ) = .orR ρ := rfl
@[simp] theorem rename_coextR (ρ : RTy) : rename (Sig := Sig) r (.coextR ρ) = .coextR ρ := rfl
@[simp] theorem rename_boxR (ρ : RTy) : rename (Sig := Sig) r (.boxR ρ) = .boxR ρ := rfl
@[simp] theorem rename_inclR (ρ : RTy) : rename (Sig := Sig) r (.inclR ρ) = .inclR ρ := rfl
end

/-- Weakening: the same term, with a new innermost variable it does not mention. -/
abbrev weaken {Γ : Ctx} {τ σ : Ty} (a : Term Sig Γ σ) : Term Sig (τ :: Γ) σ := a.rename Ren.shift

theorem rename_id : ∀ {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ), a.rename Ren.id = a
  | _, _, .var _ | _, _, .const _ | _, _, .and | _, _, .or | _, _, .not
  | _, _, .all _ | _, _, .ex _ | _, _, .eq _ | _, _, .constR _ | _, _, .negR _ | _, _, .andR _
  | _, _, .orR _ | _, _, .coextR _ | _, _, .boxR _ | _, _, .inclR _ => rfl
  | _, _, .app f a => by simp [rename_id f, rename_id a]
  | _, _, .lam b => by simp [Ren.lift_id, rename_id b]

theorem rename_rename : ∀ {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (r' : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.rename r').rename r = a.rename (Ren.comp r r')
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ | _, _, _, _, _, _, .constR _
  | _, _, _, _, _, _, .negR _ | _, _, _, _, _, _, .andR _ | _, _, _, _, _, _, .orR _
  | _, _, _, _, _, _, .coextR _ | _, _, _, _, _, _, .boxR _ | _, _, _, _, _, _, .inclR _ => rfl
  | _, _, _, r, r', _, .app f a => by simp [rename_rename r r' f, rename_rename r r' a]
  | _, _, _, r, r', _, .lam b => by
    simp [rename_rename (Ren.lift r) (Ren.lift r') b, Ren.lift_comp]

end Term

/-! ### Substitution -/

/-- A substitution: a type-preserving map from the variables of one context to terms over
another. -/
def Sub (Sig : Signature) (Γ Δ : Ctx) : Type := ∀ σ : Ty, Var Γ σ → Term Sig Δ σ

namespace Sub

variable {Sig : Signature} {Γ Δ Θ : Ctx}

/-- The identity substitution. -/
def id : Sub Sig Γ Γ := fun _ v => .var v

/-- Push a substitution under a binder: the new variable is kept, the rest are weakened. -/
def lift (s : Sub Sig Γ Δ) {σ : Ty} : Sub Sig (σ :: Γ) (σ :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => (s _ v).weaken

/-- Extend a substitution with a term for a new innermost variable. -/
def cons {σ : Ty} (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) : Sub Sig (σ :: Γ) Δ
  | _, .zero => a
  | _, .succ v => s _ v

/-- A renaming, as a substitution. -/
def ofRen (r : Ren Γ Δ) : Sub Sig Γ Δ := fun _ v => .var (r _ v)

@[simp] theorem lift_zero (s : Sub Sig Γ Δ) {σ : Ty} : Sub.lift s (σ := σ) _ .zero = .var .zero := rfl
@[simp] theorem lift_succ (s : Sub Sig Γ Δ) {σ τ : Ty} (v : Var Γ σ) :
    Sub.lift s (σ := τ) _ (.succ v) = (s _ v).weaken := rfl
@[simp] theorem cons_zero {σ : Ty} (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) : cons a s _ .zero = a := rfl
@[simp] theorem cons_succ {σ τ : Ty} (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) (v : Var Γ τ) :
    cons a s _ (.succ v) = s _ v := rfl

theorem lift_id {σ : Ty} : Sub.lift (Sub.id : Sub Sig Γ Γ) (σ := σ) = Sub.id := by
  funext τ v; cases v <;> rfl

theorem lift_ofRen (r : Ren Γ Δ) {σ : Ty} :
    Sub.lift (ofRen r : Sub Sig Γ Δ) (σ := σ) = ofRen (Ren.lift r) := by
  funext τ v; cases v <;> rfl

end Sub

namespace Term

variable {Sig : Signature}

/-- Apply a substitution to a term, by structural recursion: the implementation of `subst`. -/
def substImpl : ∀ {Γ Δ : Ctx}, Sub Sig Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Term Sig Δ σ
  | _, _, s, _, .var v => s _ v
  | _, _, _, _, .const c => .const c
  | _, _, s, _, .app f a => .app (substImpl s f) (substImpl s a)
  | _, _, s, _, .lam b => .lam (substImpl (Sub.lift s) b)
  | _, _, _, _, .and => .and
  | _, _, _, _, .or => .or
  | _, _, _, _, .not => .not
  | _, _, _, _, .all σ => .all σ
  | _, _, _, _, .ex σ => .ex σ
  | _, _, _, _, .eq σ => .eq σ
  | _, _, _, _, .constR ρ => .constR ρ
  | _, _, _, _, .negR ρ => .negR ρ
  | _, _, _, _, .andR ρ => .andR ρ
  | _, _, _, _, .orR ρ => .orR ρ
  | _, _, _, _, .coextR ρ => .coextR ρ
  | _, _, _, _, .boxR ρ => .boxR ρ
  | _, _, _, _, .inclR ρ => .inclR ρ

/-- Apply a substitution to a term. Through `Term.rec`, as `rename` is, and for the same
reason. -/
@[implemented_by substImpl]
def subst : ∀ {Γ Δ : Ctx}, Sub Sig Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Term Sig Δ σ :=
  fun {_ Δ} s {_} t =>
    Term.rec (motive := fun Γ σ _ => ∀ Δ : Ctx, Sub Sig Γ Δ → Term Sig Δ σ)
      (var := fun v _ s => s _ v)
      (const := fun c _ _ => Term.const c)
      (app := fun _ _ f a Δ' s => Term.app (f Δ' s) (a Δ' s))
      (lam := fun _ b _ s => Term.lam (b _ (Sub.lift s)))
      (and := fun _ _ => Term.and) (or := fun _ _ => Term.or) (not := fun _ _ => Term.not)
      (all := fun σ _ _ => Term.all σ) (ex := fun σ _ _ => Term.ex σ) (eq := fun σ _ _ => Term.eq σ)
      (constR := fun ρ _ _ => Term.constR ρ) (negR := fun ρ _ _ => Term.negR ρ)
      (andR := fun ρ _ _ => Term.andR ρ) (orR := fun ρ _ _ => Term.orR ρ)
      (coextR := fun ρ _ _ => Term.coextR ρ) (boxR := fun ρ _ _ => Term.boxR ρ)
      (inclR := fun ρ _ _ => Term.inclR ρ)
      t Δ s

section
variable {Γ Δ : Ctx} (s : Sub Sig Γ Δ)
@[simp] theorem subst_var {σ : Ty} (v : Var Γ σ) : subst s (.var v) = s _ v := rfl
@[simp] theorem subst_const (c : Sig.Const) : subst s (.const c) = .const c := rfl
@[simp] theorem subst_app {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    subst s (.app f a) = .app (subst s f) (subst s a) := rfl
@[simp] theorem subst_lam {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    subst s (.lam b) = .lam (subst (Sub.lift s) b) := rfl
@[simp] theorem subst_and : subst (Sig := Sig) s .and = .and := rfl
@[simp] theorem subst_or : subst (Sig := Sig) s .or = .or := rfl
@[simp] theorem subst_not : subst (Sig := Sig) s .not = .not := rfl
@[simp] theorem subst_all (σ : Ty) : subst (Sig := Sig) s (.all σ) = .all σ := rfl
@[simp] theorem subst_ex (σ : Ty) : subst (Sig := Sig) s (.ex σ) = .ex σ := rfl
@[simp] theorem subst_eq (σ : Ty) : subst (Sig := Sig) s (.eq σ) = .eq σ := rfl
@[simp] theorem subst_constR (ρ : RTy) : subst (Sig := Sig) s (.constR ρ) = .constR ρ := rfl
@[simp] theorem subst_negR (ρ : RTy) : subst (Sig := Sig) s (.negR ρ) = .negR ρ := rfl
@[simp] theorem subst_andR (ρ : RTy) : subst (Sig := Sig) s (.andR ρ) = .andR ρ := rfl
@[simp] theorem subst_orR (ρ : RTy) : subst (Sig := Sig) s (.orR ρ) = .orR ρ := rfl
@[simp] theorem subst_coextR (ρ : RTy) : subst (Sig := Sig) s (.coextR ρ) = .coextR ρ := rfl
@[simp] theorem subst_boxR (ρ : RTy) : subst (Sig := Sig) s (.boxR ρ) = .boxR ρ := rfl
@[simp] theorem subst_inclR (ρ : RTy) : subst (Sig := Sig) s (.inclR ρ) = .inclR ρ := rfl
end

/-- `b[a]`: substitute `a` for the innermost variable of `b`. This is what a β-step
does, and what instantiating a quantifier does. -/
abbrev instantiate {Γ : Ctx} {σ τ : Ty} (b : Term Sig (σ :: Γ) τ) (a : Term Sig Γ σ) :
    Term Sig Γ τ :=
  b.subst (Sub.cons a Sub.id)

theorem subst_id : ∀ {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ), a.subst Sub.id = a
  | _, _, .var _ | _, _, .const _ | _, _, .and | _, _, .or | _, _, .not
  | _, _, .all _ | _, _, .ex _ | _, _, .eq _ | _, _, .constR _ | _, _, .negR _ | _, _, .andR _
  | _, _, .orR _ | _, _, .coextR _ | _, _, .boxR _ | _, _, .inclR _ => rfl
  | _, _, .app f a => by simp [subst_id f, subst_id a]
  | _, _, .lam b => by simp [Sub.lift_id, subst_id b]

/-- A renaming is the substitution that sends each variable to a variable. -/
theorem rename_eq_subst : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    a.rename r = a.subst (Sub.ofRen r)
  | _, _, _, _, .var _ | _, _, _, _, .const _ | _, _, _, _, .and | _, _, _, _, .or
  | _, _, _, _, .not | _, _, _, _, .all _ | _, _, _, _, .ex _ | _, _, _, _, .eq _
  | _, _, _, _, .constR _ | _, _, _, _, .negR _ | _, _, _, _, .andR _ | _, _, _, _, .orR _
  | _, _, _, _, .coextR _ | _, _, _, _, .boxR _ | _, _, _, _, .inclR _ => rfl
  | _, _, r, _, .app f a => by simp [rename_eq_subst r f, rename_eq_subst r a]
  | _, _, r, _, .lam b => by
    simp [rename_eq_subst (Ren.lift r) b, Sub.lift_ofRen]

/-! The four composition laws. `subst_rename` and `rename_subst` are the two mixed cases,
which the lifting lemmas need, and `subst_subst` is the one that matters downstream. -/

/-- The composite substitution `s ∘ r`, on variables. -/
def _root_.Classicism.Meta.Sub.compRen {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) : Sub Sig Γ Θ :=
  fun _ v => s _ (r _ v)
/-- The composite `r ∘ s`, applying a renaming to the terms of a substitution. -/
def _root_.Classicism.Meta.Ren.compSub {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) : Sub Sig Γ Θ :=
  fun _ v => (s _ v).rename r
/-- The composite of two substitutions. -/
def _root_.Classicism.Meta.Sub.comp {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) : Sub Sig Γ Θ :=
  fun _ v => (s' _ v).subst s

theorem _root_.Classicism.Meta.Sub.lift_compRen {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) {σ : Ty} :
    Sub.lift (Sub.compRen s r) (σ := σ) = Sub.compRen (Sub.lift s) (Ren.lift r) := by
  funext τ v; cases v <;> rfl

theorem subst_rename : ∀ {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.rename r).subst s = a.subst (Sub.compRen s r)
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ | _, _, _, _, _, _, .constR _
  | _, _, _, _, _, _, .negR _ | _, _, _, _, _, _, .andR _ | _, _, _, _, _, _, .orR _
  | _, _, _, _, _, _, .coextR _ | _, _, _, _, _, _, .boxR _ | _, _, _, _, _, _, .inclR _ => rfl
  | _, _, _, s, r, _, .app f a => by simp [subst_rename s r f, subst_rename s r a]
  | _, _, _, s, r, _, .lam b => by
    simp [subst_rename (Sub.lift s) (Ren.lift r) b, Sub.lift_compRen]

theorem _root_.Classicism.Meta.Ren.lift_compSub {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) {σ : Ty} :
    Sub.lift (Ren.compSub r s) (σ := σ) = Ren.compSub (Ren.lift r) (Sub.lift s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
    show ((s _ v).rename r).weaken = ((s _ v).weaken).rename (Ren.lift r)
    simp only [weaken, rename_rename]
    rfl

theorem rename_subst : ∀ {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.subst s).rename r = a.subst (Ren.compSub r s)
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ | _, _, _, _, _, _, .constR _
  | _, _, _, _, _, _, .negR _ | _, _, _, _, _, _, .andR _ | _, _, _, _, _, _, .orR _
  | _, _, _, _, _, _, .coextR _ | _, _, _, _, _, _, .boxR _ | _, _, _, _, _, _, .inclR _ => rfl
  | _, _, _, r, s, _, .app f a => by simp [rename_subst r s f, rename_subst r s a]
  | _, _, _, r, s, _, .lam b => by
    simp [rename_subst (Ren.lift r) (Sub.lift s) b, Ren.lift_compSub]

theorem _root_.Classicism.Meta.Sub.lift_comp {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) {σ : Ty} :
    Sub.lift (Sub.comp s s') (σ := σ) = Sub.comp (Sub.lift s) (Sub.lift s') := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
    show ((s' _ v).subst s).weaken = ((s' _ v).weaken).subst (Sub.lift s)
    simp only [weaken, rename_subst, subst_rename]
    rfl

theorem subst_subst : ∀ {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.subst s').subst s = a.subst (Sub.comp s s')
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ | _, _, _, _, _, _, .constR _
  | _, _, _, _, _, _, .negR _ | _, _, _, _, _, _, .andR _ | _, _, _, _, _, _, .orR _
  | _, _, _, _, _, _, .coextR _ | _, _, _, _, _, _, .boxR _ | _, _, _, _, _, _, .inclR _ => rfl
  | _, _, _, s, s', _, .app f a => by simp [subst_subst s s' f, subst_subst s s' a]
  | _, _, _, s, s', _, .lam b => by
    simp [subst_subst (Sub.lift s) (Sub.lift s') b, Sub.lift_comp]

/-- Substituting under a `cons` into a weakened term drops the `cons`. -/
@[simp] theorem _root_.Classicism.Meta.Sub.compRen_cons_shift {Γ Δ : Ctx} {σ : Ty}
    (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) :
    Sub.compRen (Sub.cons a s) (Ren.shift (σ := σ)) = s := by
  funext τ v; rfl

/-- Substituting into a weakened term, for the innermost variable, does nothing. -/
theorem instantiate_weaken {Γ : Ctx} {σ τ : Ty} (a : Term Sig Γ τ) (b : Term Sig Γ σ) :
    (a.weaken (τ := σ)).instantiate b = a := by
  rw [instantiate, weaken, subst_rename, Sub.compRen_cons_shift]
  exact subst_id a

end Term

end Classicism.Meta
