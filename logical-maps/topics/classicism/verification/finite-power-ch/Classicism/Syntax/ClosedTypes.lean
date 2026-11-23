import Classicism.Syntax.Entailment

/-!
# The paper's language inside the object language

The object language has type variables besides the paper's types (`Syntax/Types.lean`), a
device of the metalogic: the vectorization theorem instantiates them. A sentence of the
**paper's language** is one in which every type is closed, `Term.closedTypes`
(`Syntax/Term.lean`), and the map's sentence schemas range over those only. This module
has the predicate on schemas, `AxiomSet.ClosedTypes`, and the facts that the connectives
and quantifiers keep a formula in the paper's language, which the proofs building
instances of the sentence schemas use. That every schema of a principle of the map is in
the paper's language is `P.X.schema_closedTypes` (`Certified/Schemas.lean`).
-/

namespace Classicism.Meta

namespace AxiomSet

variable {Sig : Signature}

/-- A schema of sentences of the paper's language: every type in them closed. -/
def ClosedTypes (Ax : AxiomSet Sig) : Prop := ∀ a, Ax a → a.closedTypes = true

theorem ClosedTypes.mono {A B : AxiomSet Sig} (h : A ⊆ B) (hB : ClosedTypes B) : ClosedTypes A :=
  fun a ha => hB a (h a ha)

/-- A **complete** theory: it decides every sentence of the paper's language. A consistent
complete theory is the syntactic form of a single model: what it does not entail of a
schema, it refutes at some instance, and all those refutations hold together. The map's
model statements ask for one (the topic's `lean.model` shape): a consistent theory merely not entailing
each violated schema could fail to entail both a sentence and its negation. -/
def Complete (Ax : AxiomSet Sig) : Prop :=
  ∀ p : Sentence Sig, p.closedTypes = true →
    Theorem (C.axioms ∪ Ax) p ∨ Theorem (C.axioms ∪ Ax) (Term.neg p)

theorem ClosedTypes.union {A B : AxiomSet Sig} (hA : ClosedTypes A) (hB : ClosedTypes B) :
    ClosedTypes (A ∪ B) := fun a ha => ha.elim (hA a) (hB a)

end AxiomSet

namespace Term

variable {Sig : Signature}

/-! ### The connectives and quantifiers keep a formula in the paper's language -/

@[simp] theorem closedTypes_neg {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.neg p).closedTypes = p.closedTypes := by
  simp [Term.closedTypes, Term.neg]
@[simp] theorem closedTypes_conj {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.conj p q).closedTypes = (p.closedTypes && q.closedTypes) := by
  simp [Term.closedTypes, Term.conj]
@[simp] theorem closedTypes_disj {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.disj p q).closedTypes = (p.closedTypes && q.closedTypes) := by
  simp [Term.closedTypes, Term.disj]
@[simp] theorem closedTypes_imp {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.imp p q).closedTypes = (p.closedTypes && q.closedTypes) := by
  simp [Term.closedTypes, Term.imp, Term.disj, Term.neg]
@[simp] theorem closedTypes_iff {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.iff p q).closedTypes = (p.closedTypes && q.closedTypes) := by
  simp [Term.iff, Bool.and_comm, Bool.and_left_comm]
@[simp] theorem closedTypes_eq' {Γ : Ctx} {σ : Ty} (x y : Term Sig Γ σ) :
    (Term.eq' x y).closedTypes = (x.closedTypes && y.closedTypes) := by
  cases hx : x.closedTypes
  · simp [Term.closedTypes, Term.eq', hx]
  · simp [Term.closedTypes, Term.eq', hx, Term.closed_of_closedTypes hx]
@[simp] theorem closedTypes_var {Γ : Ctx} {σ : Ty} (v : Var Γ σ) :
    (Term.var v : Term Sig Γ σ).closedTypes = decide σ.Closed := rfl
@[simp] theorem closedTypes_forall' {Γ : Ctx} {σ : Ty} (p : Formula Sig (σ :: Γ)) :
    (Term.forall' p).closedTypes = (decide σ.Closed && p.closedTypes) := by
  simp only [Term.forall', Term.closedTypes]; cases decide σ.Closed <;> simp
@[simp] theorem closedTypes_exists' {Γ : Ctx} {σ : Ty} (p : Formula Sig (σ :: Γ)) :
    (Term.exists' p).closedTypes = (decide σ.Closed && p.closedTypes) := by
  simp only [Term.exists', Term.closedTypes]; cases decide σ.Closed <;> simp
@[simp] theorem closedTypes_top {Γ : Ctx} : (Term.top : Formula Sig Γ).closedTypes = true := rfl
@[simp] theorem closedTypes_bot {Γ : Ctx} : (Term.bot : Formula Sig Γ).closedTypes = true := rfl
@[simp] theorem closedTypes_box {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.box p).closedTypes = p.closedTypes := by
  rw [Term.box, closedTypes_eq', closedTypes_top, Bool.and_true]
@[simp] theorem closedTypes_dia {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.dia p).closedTypes = p.closedTypes := by
  rw [Term.dia, closedTypes_neg, closedTypes_eq', closedTypes_bot, Bool.and_true]

/-! ### Renaming and substitution keep a term in the paper's language

A renaming sends each variable to one of the same type, and so keeps every type of the
term. So does a substitution that puts for each variable a term of the paper's language
just when the variable's type is closed (`Sub.KeepsTypes`): constants do, and variables. -/

theorem closedTypes_rename : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (t : Term Sig Γ σ),
    (t.rename r).closedTypes = t.closedTypes
  | _, _, _, _, .var _ | _, _, _, _, .const _ | _, _, _, _, .and | _, _, _, _, .or
  | _, _, _, _, .not | _, _, _, _, .all _ | _, _, _, _, .ex _ | _, _, _, _, .eq _
  | _, _, _, _, .constR _ | _, _, _, _, .negR _ | _, _, _, _, .andR _ | _, _, _, _, .orR _
  | _, _, _, _, .coextR _ | _, _, _, _, .boxR _ | _, _, _, _, .inclR _ => rfl
  | _, _, r, _, .app f a => by
    simp only [rename_app, closedTypes, closedTypes_rename r f, closedTypes_rename r a]
  | _, _, r, _, .lam b => by
    simp only [rename_lam, closedTypes, closedTypes_rename (Ren.lift r) b]

end Term

/-- A substitution keeps the paper's language when what it puts for each variable is in the
language just when the variable's type is closed. -/
def Sub.KeepsTypes {Γ Δ : Ctx} (s : Sub Sig Γ Δ) : Prop :=
  ∀ σ (v : Var Γ σ), (s σ v).closedTypes = decide σ.Closed

theorem Sub.KeepsTypes.id {Γ : Ctx} : (Sub.id : Sub Sig Γ Γ).KeepsTypes := fun _ _ => rfl

theorem Sub.KeepsTypes.lift {Γ Δ : Ctx} {s : Sub Sig Γ Δ} (h : s.KeepsTypes) {τ : Ty} :
    (Sub.lift s (σ := τ)).KeepsTypes
  | _, .zero => rfl
  | _, .succ v => by
    simp only [Sub.lift_succ, Term.weaken, Term.closedTypes_rename]; exact h _ v

theorem Sub.KeepsTypes.cons {Γ Δ : Ctx} {σ : Ty} {a : Term Sig Δ σ} {s : Sub Sig Γ Δ}
    (ha : a.closedTypes = decide σ.Closed) (h : s.KeepsTypes) : (Sub.cons a s).KeepsTypes
  | _, .zero => ha
  | _, .succ v => h _ v

namespace Term

theorem closedTypes_subst : ∀ {Γ Δ : Ctx} (s : Sub Sig Γ Δ), s.KeepsTypes → ∀ {σ : Ty}
    (t : Term Sig Γ σ), (t.subst s).closedTypes = t.closedTypes
  | _, _, s, h, _, .var v => h _ v
  | _, _, _, _, _, .const _ | _, _, _, _, _, .and | _, _, _, _, _, .or
  | _, _, _, _, _, .not | _, _, _, _, _, .all _ | _, _, _, _, _, .ex _ | _, _, _, _, _, .eq _
  | _, _, _, _, _, .constR _ | _, _, _, _, _, .negR _ | _, _, _, _, _, .andR _
  | _, _, _, _, _, .orR _ | _, _, _, _, _, .coextR _ | _, _, _, _, _, .boxR _
  | _, _, _, _, _, .inclR _ => rfl
  | _, _, s, h, _, .app f a => by
    simp only [subst_app, closedTypes, closedTypes_subst s h f, closedTypes_subst s h a]
  | _, _, s, h, _, .lam b => by
    simp only [subst_lam, closedTypes, closedTypes_subst (Sub.lift s) h.lift b]

end Term

end Classicism.Meta
