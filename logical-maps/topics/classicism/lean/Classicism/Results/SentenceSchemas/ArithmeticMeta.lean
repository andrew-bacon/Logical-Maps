import Classicism.Results.SentenceSchemas.Arithmetic

/-!
# `C5` gives the Necessity of Arithmetic: the induction

`c5-implies-necessity-of-arithmetic`. For a type `σ` and an arithmetical formula `A` in `k`
number variables, `NC(A) := (A → □A) ∧ (¬A → □¬A)` is derivable in `C` with `□ND` from the
hypotheses that the `k` variables are numbers (`numHyps`), by induction on `A`: each case is the
derivation of a step of `Arithmetic.lean`, instantiated at the quoted vocabulary and at the
subformulas, its equations discharged by reflexivity. For a sentence there are no hypotheses, and
the last step turns `NC(A)` into `□(I → A) ∨ □(I → ¬A)`.

The quantifier case is the one place a conversion is needed: the step's property variable is
instantiated at `λv. A`, and `(λv. A) v` is `A` by β.
-/

noncomputable section

namespace Classicism.Meta

open AxiomSet

/-- The axioms of `C5`: `C` with `□ND` at every closed type. -/
abbrev C5Ax : AxiomSet Signature.pure := C.axioms ∪ P.NecNecessityOfDistinctness.schema

/-- Non-contingency of a formula: `(p → □p) ∧ (¬p → □¬p)`. -/
abbrev NCt {Γ : Ctx} (p : Formula Signature.pure Γ) : Formula Signature.pure Γ :=
  Term.conj (Term.imp p (Term.box p)) (Term.imp (Term.neg p) (Term.box (Term.neg p)))

/-- `ℕt`, for a term `t` of the type of numbers at `σ`. -/
abbrev Nt (σ : Ty) {Γ : Ctx} (t : Term Signature.pure Γ (Ty.nu σ)) : Formula Signature.pure Γ :=
  .app (Arith.N.term σ).close t

/-! ### Syntax -/

theorem Ren.comp_ofEmpty {Γ Δ : Ctx} (r : Ren Γ Δ) : Ren.comp r Ren.ofEmpty = Ren.ofEmpty :=
  funext fun _ => funext fun v => nomatch v

/-- A closed term is unchanged by renaming. -/
theorem Term.close_rename {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (a : Term Signature.pure [] σ) :
    (a.close : Term Signature.pure Γ σ).rename r = a.close := by
  show (a.rename Ren.ofEmpty).rename r = a.rename Ren.ofEmpty
  rw [Term.rename_rename, Ren.comp_ofEmpty]

/-- Instantiating the innermost variable of a term lifted over it gives the term back:
`b↑[v₀] = b`. -/
theorem Term.instantiate_rename_lift_shift {Γ : Ctx} {σ τ : Ty} (b : Term Signature.pure (σ :: Γ) τ) :
    (b.rename (Ren.lift Ren.shift)).instantiate (.var .zero) = b := by
  show (b.rename (Ren.lift Ren.shift)).subst (Sub.cons (.var .zero) Sub.id) = b
  rw [Term.subst_rename]
  conv_rhs => rw [← Term.subst_id b]
  congr 1
  funext υ v
  cases v <;> rfl

/-- `(λv. b)↑ v₀ ≡ b`: a lambda weakened under a binder and applied to its variable. -/
theorem Conv.app_lam_weaken_var {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Signature.pure (σ :: Γ) ρ) :
    Term.app (Term.lam (b.rename (Ren.lift Ren.shift))) (.var .zero) ≡ b := by
  have h := Conv.beta (b.rename (Ren.lift Ren.shift)) (.var .zero)
  rwa [Term.instantiate_rename_lift_shift] at h

/-- Conversion passes through `NC`. -/
theorem Conv.nct {Γ : Ctx} {p q : Formula Signature.pure Γ} (h : p ≡ q) : NCt p ≡ NCt q := by
  repeat' first | exact h | exact Conv.refl _ | apply Conv.app_congr

/-! ### The hypotheses that the variables are numbers -/

/-- `ℕv₀, …, ℕvₖ₋₁`, in the context of `k` number variables. -/
def numHyps (σ : Ty) : ∀ k : Nat, List (Formula Signature.pure (numCtx σ k))
  | 0 => []
  | k + 1 => Nt σ (.var (.zero (Γ := numCtx σ k))) :: Hyps.weaken (numHyps σ k)

theorem mem_numHyps (σ : Ty) : ∀ {k : Nat} (i : Fin k), Nt σ (.var (numVar σ i)) ∈ numHyps σ k
  | k + 1, ⟨0, _⟩ => List.mem_cons_self ..
  | k + 1, ⟨i + 1, h⟩ => by
    apply List.mem_cons_of_mem
    refine List.mem_map.2 ⟨Nt σ (.var (numVar σ ⟨i, Nat.lt_of_succ_lt_succ h⟩)),
      mem_numHyps σ ⟨i, Nat.lt_of_succ_lt_succ h⟩, ?_⟩
    show Term.rename Ren.shift (Term.app _ _) = _
    rw [Term.rename_app, Term.rename_var, Term.close_rename]
    rfl

/-! ### `C5` supplies `B`, `BF` at the type of numbers and `ND` there -/

/-- `□ND` at a closed type, as an axiom of `C5`. -/
theorem c5_at (σ : Ty) (hσ : σ.Closed) : Theorem C5Ax (P.NecNecessityOfDistinctness.quoted σ) :=
  Theorem.ax ⟨σ, hσ, rfl⟩

/-- `B`, from `□ND` at `t`: `∀p. p → □◇p`. -/
theorem c5_B_thm : Theorem C5Ax (Term.forall' (σ := Ty.rel RTy.t)
    (Term.imp Term.v0 (Term.box (Term.dia Term.v0)))) :=
  Theorem.mp (Theorem.ofCMinus c5_b.derivable) (c5_at (Ty.rel RTy.t) (by simp))

/-- `BF` at the type of numbers: `∀X. (∀x. □Xx) → □∀x. Xx`. -/
theorem c5_BF_thm (σ : Ty) : Theorem C5Ax (Term.forall' (σ := Ty.nu σ ⇒ RTy.t)
    (Term.imp (Term.forall' (σ := Ty.nu σ) (Term.box (Term.app Term.v1 Term.v0)))
      (Term.box (Term.forall' (σ := Ty.nu σ) (Term.app Term.v1 Term.v0))))) :=
  Theorem.mp (Theorem.ofCMinus (c5_bf_nu.derivable σ)) (c5_at (Ty.rel RTy.t) (by simp))

/-- `ND` at the type of numbers: `∀x y. x ≠ y → □(x ≠ y)`. -/
theorem c5_ND_thm (σ : Ty) : Theorem C5Ax (Term.forall' (σ := Ty.nu σ) (Term.forall' (σ := Ty.nu σ)
    (Term.imp (Term.neg (Term.eq' Term.v1 Term.v0))
      (Term.box (Term.neg (Term.eq' Term.v1 Term.v0)))))) :=
  Theorem.mp (Theorem.ofCMinus (c5_nd_nu.derivable σ)) (c5_at (Ty.rel RTy.t) (by simp))

/-! ### The induction -/

/-- A term of arithmetic is a number, given that its variables are. -/
theorem nat_of_aterm (σ : Ty) : ∀ {k : Nat} (t : ATerm k),
    Derivable C5Ax (numHyps σ k) (Nt σ (t.toTerm σ))
  | _, .var i => Derivable.hyp (mem_numHyps σ i)
  | _, .zero =>
    Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem (Theorem.ofCMinus (arith_N_zero_rel.derivable σ)))
        (Arith.N.term σ).close (Arith.zero.term σ).close)
      (Derivable.refl _)) (Derivable.refl _)
  | _, .suc t =>
    Derivable.impE (Derivable.impE (Derivable.impE
      (Derivable.allE₃β (Derivable.ofTheorem (Theorem.ofCMinus (arith_N_suc_rel.derivable σ)))
        (Arith.N.term σ).close (Arith.suc.term σ).close (t.toTerm σ))
      (Derivable.refl _)) (Derivable.refl _)) (nat_of_aterm σ t)

/-- **An arithmetical formula is non-contingent**, in `C5`, given that its variables are
numbers. -/
theorem nc_of_aform (σ : Ty) : ∀ {k : Nat} (φ : AForm k),
    Derivable C5Ax (numHyps σ k) (NCt (φ.toTerm σ))
  | _, .nat t =>
    Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem (Theorem.ofCMinus (arith_nc_N_rel.derivable σ)))
        (Arith.N.term σ).close (t.toTerm σ))
      (Derivable.ofTheorem c5_B_thm)) (Derivable.refl _)
  | _, .sum t u v =>
    Derivable.impE (Derivable.impE
      (Derivable.allE₃β
        (Derivable.allEβ (Derivable.ofTheorem (Theorem.ofCMinus (arith_nc_Sum_rel.derivable σ)))
          (Arith.Sum.term σ).close)
        (t.toTerm σ) (u.toTerm σ) (v.toTerm σ))
      (Derivable.ofTheorem c5_B_thm)) (Derivable.refl _)
  | _, .prod t u v =>
    Derivable.impE (Derivable.impE
      (Derivable.allE₃β
        (Derivable.allEβ (Derivable.ofTheorem (Theorem.ofCMinus (arith_nc_Prod_rel.derivable σ)))
          (Arith.Prod.term σ).close)
        (t.toTerm σ) (u.toTerm σ) (v.toTerm σ))
      (Derivable.ofTheorem c5_B_thm)) (Derivable.refl _)
  | _, .eq t u =>
    Derivable.allE₂β
      (Derivable.ofTheorem (Theorem.mp (Theorem.ofCMinus (arith_nc_eq.derivable σ)) (c5_ND_thm σ)))
      (t.toTerm σ) (u.toTerm σ)
  | _, .neg φ =>
    Derivable.impE
      (Derivable.allEβ (Derivable.ofTheorem (Theorem.ofCMinus nc_neg.derivable)) (φ.toTerm σ))
      (nc_of_aform σ φ)
  | _, .disj φ ψ =>
    Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem (Theorem.ofCMinus nc_disj.derivable))
        (φ.toTerm σ) (ψ.toTerm σ))
      (nc_of_aform σ φ)) (nc_of_aform σ ψ)
  | _, .conj φ ψ =>
    Derivable.impE (Derivable.impE
      (Derivable.allE₂β (Derivable.ofTheorem (Theorem.ofCMinus nc_conj.derivable))
        (φ.toTerm σ) (ψ.toTerm σ))
      (nc_of_aform σ φ)) (nc_of_aform σ ψ)
  | _, .all φ =>
    Derivable.conv
      (Derivable.impE (Derivable.impE (Derivable.impE (Derivable.impE
        (Derivable.allE₂β (Derivable.ofTheorem (Theorem.ofCMinus (nc_all_rel.derivable σ)))
          (Arith.N.term σ).close (Term.lam (φ.toTerm σ)))
        (Derivable.ofTheorem (c5_BF_thm σ))) (Derivable.ofTheorem c5_B_thm)) (Derivable.refl _))
        (Derivable.conv (Derivable.allI (Derivable.impI (nc_of_aform σ φ)))
          (Conv.app_congr (Conv.refl _) (Conv.lam_congr (Conv.app_congr (Conv.refl _)
            (Conv.nct (Conv.symm (Conv.app_lam_weaken_var _))))))))
      (Conv.nct (Conv.app_congr (Conv.refl _) (Conv.lam_congr (Conv.app_congr (Conv.refl _)
        (Conv.app_lam_weaken_var _)))))

/-- **`C5` gives the Necessity of Arithmetic** (Bacon, Theorem 4.4, in the map's formulation):
for each arithmetical sentence `A` read at `σ`, `□(I_σ → A) ∨ □(I_σ → ¬A)`, from `NC(A)`. -/
theorem c5_entails_necessityOfArithmetic :
    P.NecNecessityOfDistinctness.schema ⟹ necessityOfArithmetic := by
  rintro _ ⟨σ, _, A, rfl⟩
  exact Theorem.mp
    (Derivable.allE₂β (Theorem.ofCMinus nc_final.derivable) (A.toTerm σ) (arithI σ))
    (nc_of_aform σ A)

end Classicism.Meta

end
