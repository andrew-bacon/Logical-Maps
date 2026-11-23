import Classicism.Semantics.Relational

/-! One-constructor denotation equations, checked generically so concrete
reflection need not unfold the recursive interpreter on a whole large term.
OpenAI Codex, prompted by Andrew Bacon, 1 November 2026. -/
namespace Classicism.Meta.DenotationSteps
variable {Sig : Signature} (I : Interp Sig) {Γ : Ctx}

theorem app {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ))
    (a : Term Sig Γ σ) (env : Env I.D Γ) :
    (Term.app f a).denote I env = (f.denote I env) (a.denote I env) := rfl
theorem lam {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) (env : Env I.D Γ) :
    (Term.lam b).denote I env = (fun x => b.denote I (.cons x env)) := rfl
theorem var {σ : Ty} (v : Var Γ σ) (env : Env I.D Γ) :
    (Term.var v).denote I env = v.denote env := rfl
theorem const (c : Sig.Const) (env : Env I.D Γ) :
    (Term.const c).denote I env = I.const c := rfl
theorem and (env : Env I.D Γ) : Term.and.denote I env = (fun p q => p ∧ q) := rfl
theorem or (env : Env I.D Γ) : Term.or.denote I env = (fun p q => p ∨ q) := rfl
theorem not (env : Env I.D Γ) : Term.not.denote I env = (fun p => ¬ p) := rfl
theorem all (σ : Ty) (env : Env I.D Γ) :
    (Term.all σ).denote I env = (fun F => ∀ x, F x) := rfl
theorem ex (σ : Ty) (env : Env I.D Γ) :
    (Term.ex σ).denote I env = (fun F => ∃ x, F x) := rfl
theorem eq (σ : Ty) (env : Env I.D Γ) :
    (Term.eq σ).denote I env = (fun a b => a = b) := rfl
theorem constR (ρ : RTy) (env : Env I.D Γ) :
    (Term.constR ρ).denote I env = RTy.constD I.D ρ := rfl
theorem negR (ρ : RTy) (env : Env I.D Γ) :
    (Term.negR ρ).denote I env = RTy.negD I.D ρ := rfl
theorem andR (ρ : RTy) (env : Env I.D Γ) :
    (Term.andR ρ).denote I env = RTy.andD I.D ρ := rfl
theorem orR (ρ : RTy) (env : Env I.D Γ) :
    (Term.orR ρ).denote I env = RTy.orD I.D ρ := rfl
theorem coextR (ρ : RTy) (env : Env I.D Γ) :
    (Term.coextR ρ).denote I env = RTy.coextD I.D ρ := rfl
theorem boxR (ρ : RTy) (env : Env I.D Γ) :
    (Term.boxR ρ).denote I env = RTy.boxD I.D ρ := rfl
theorem inclR (ρ : RTy) (env : Env I.D Γ) :
    (Term.inclR ρ).denote I env = RTy.inclD I.D ρ := rfl
end Classicism.Meta.DenotationSteps
