import Classicism.Semantics.Denotation
import Classicism.Strict.Mirror

/-!
# The relational operations, in the object language

The paper writes the Boolean operations, coextension, and the pointwise box at every
relational type with a type subscript, `∧_τ`, `¬_τ`, and defines each by recursion on the
type: at `t` it is the propositional operation, at `σ → ρ` it is the operation at `ρ`
applied pointwise. The shallow layer carries these as the class `Rel`, with an instance
per shape of type. In the object language they are **constants of the syntax with an
unfolding rule**, `Term.andR ρ` and the rest of `Term.lean`, the recursive definition
read as the δ-rule of conversion (`Conversion.lean`): `∧_t ≡ ∧`, and
`∧_{σ→ρ} ≡ λX Y z. X z ∧_ρ Y z`.

Constants rather than functions defined by recursion on the type, which is what they
were first: a function stuck at a type *variable* is not a node of the syntax, so
renaming and substitution could not pass through it, and no derivation could mention
`∧_τ` for `τ` a variable — which is exactly what a derivation by induction on the type
must do. As constants they are what the paper's subscripted symbols are, and their
recursion is a matter of conversion, not of the syntax.

Their reading (`Denotation.lean`) is the same recursion on the Lean side. The bridge to
the shallow layer is `instRelDenote`, which equips the standard reading of each relational
type with its `Rel` instance by that recursion, and one lemma per operation, proved by
induction on the type, saying that reading `∧_τ` back gives `Rel.and`. These are what
let the quoter handle a shallow statement with a parameter `[Rel τ]`: the operations at
the type parameter `τ` become `andR τ'` and the rest, and reflection, no longer `rfl`, is
these lemmas.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-! ### The standard reading carries the shallow layer's instances -/

/-- The `Rel` instance on the reading of a relational type. -/
instance instRelDenote (D : Type) : ∀ τ : RTy, Classicism.Rel (RTy.denote D τ)
  | .t => Classicism.instRelProp
  | .arr _ ρ => @Classicism.instRelArrow _ _ ⟨()⟩ (instRelDenote D ρ)

instance instOrderDenote (D : Type) : ∀ τ : RTy,
    @Classicism.Order (RTy.denote D τ) (instRelDenote D τ)
  | .t => Classicism.instOrderProp
  | .arr _ ρ => @Classicism.instOrderArrow _ _ ⟨()⟩ (instRelDenote D ρ) (instOrderDenote D ρ)

instance instPointwiseDenote (D : Type) : ∀ τ : RTy,
    @Classicism.Pointwise (RTy.denote D τ) (instRelDenote D τ)
  | .t => Classicism.instPointwiseProp
  | .arr _ ρ =>
    @Classicism.instPointwiseArrow _ _ ⟨()⟩ (instRelDenote D ρ) (instPointwiseDenote D ρ)

/-! ### Reading each operation back gives the shallow layer's

The shallow `Rel` at `Prop` reads `coext` as `↔`, `incl` as `→` and `boxAt` as
`□p := (p = True)`, where the recursions of `Denotation.lean`, following the object
syntax, read them as `(¬p ∨ q) ∧ (¬q ∨ p)`, `¬p ∨ q` and `p = ⊤` with `⊤` the sentence
`∀p.p ∨ ¬∀p.p`. The two agree by `propext`, which is what reflection of a shallow statement
rewrites with. -/

theorem top_eq : ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q) = True :=
  propext ⟨fun _ => trivial, fun _ => Classical.em _⟩
theorem bot_eq : ((∀ q : Prop, q) ∧ ¬ ∀ q : Prop, q) = False :=
  propext ⟨fun ⟨h, hn⟩ => hn h, fun h => h.elim⟩
theorem imp_eq (p q : Prop) : (¬ p ∨ q) = (p → q) :=
  propext ⟨fun h hp => h.elim (fun hn => absurd hp hn) id,
    fun h => (Classical.em p).elim (fun hp => Or.inr (h hp)) Or.inl⟩
theorem iff_eq (p q : Prop) : ((¬ p ∨ q) ∧ (¬ q ∨ p)) = (p ↔ q) := by
  rw [imp_eq, imp_eq]; exact propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun h => ⟨h.1, h.2⟩⟩
theorem box_eq (p : Prop) : (p = ((∀ q : Prop, q) ∨ ¬ ∀ q : Prop, q)) = (p = True) := by
  rw [top_eq]
theorem iff_eq' (p q : Prop) : ((p → q) ∧ (q → p)) = (p ↔ q) :=
  propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun h => ⟨h.1, h.2⟩⟩

theorem RTy.constD_eq_rel (D : Type) : ∀ τ : RTy, RTy.constD D τ = @Classicism.Rel.constP _ (instRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by funext p z; exact congrFun (RTy.constD_eq_rel D ρ) p
theorem RTy.negD_eq_rel (D : Type) : ∀ τ : RTy, RTy.negD D τ = @Classicism.Rel.neg _ (instRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by funext X z; exact congrFun (RTy.negD_eq_rel D ρ) (X z)
theorem RTy.andD_eq_rel (D : Type) : ∀ τ : RTy, RTy.andD D τ = @Classicism.Rel.and _ (instRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by funext X Y z; exact congrFun (congrFun (RTy.andD_eq_rel D ρ) (X z)) (Y z)
theorem RTy.orD_eq_rel (D : Type) : ∀ τ : RTy, RTy.orD D τ = @Classicism.Rel.or _ (instRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by funext X Y z; exact congrFun (congrFun (RTy.orD_eq_rel D ρ) (X z)) (Y z)
theorem RTy.coextD_eq_rel (D : Type) : ∀ τ : RTy, RTy.coextD D τ = @Classicism.Rel.coext _ (instRelDenote D τ)
  | .t => by funext p q; exact iff_eq p q
  | .arr _ ρ => by
    funext X Y
    exact congrArg (fun r => ∀ z, r z) (funext fun z => congrFun (congrFun (RTy.coextD_eq_rel D ρ) (X z)) (Y z))
theorem RTy.boxD_eq_rel (D : Type) : ∀ τ : RTy, RTy.boxD D τ = @Classicism.Rel.boxAt _ (instRelDenote D τ)
  | .t => by funext p; exact box_eq p
  | .arr _ ρ => by funext X z; exact congrFun (RTy.boxD_eq_rel D ρ) (X z)
theorem RTy.inclD_eq_rel (D : Type) : ∀ τ : RTy, RTy.inclD D τ = @Classicism.Rel.incl _ (instRelDenote D τ)
  | .t => by funext p q; exact imp_eq p q
  | .arr _ ρ => by
    funext X Y
    exact congrArg (fun r => ∀ z, r z) (funext fun z => congrFun (congrFun (RTy.inclD_eq_rel D ρ) (X z)) (Y z))

namespace Term

variable (I : Interp Sig) {Γ : Ctx} (τ : RTy) (env : Env I.D Γ)

theorem denote_constR : (Term.constR (Sig := Sig) τ).denote I env = @Classicism.Rel.constP _ (instRelDenote I.D τ) :=
  RTy.constD_eq_rel I.D τ
theorem denote_negR : (Term.negR (Sig := Sig) τ).denote I env = @Classicism.Rel.neg _ (instRelDenote I.D τ) :=
  RTy.negD_eq_rel I.D τ
theorem denote_andR : (Term.andR (Sig := Sig) τ).denote I env = @Classicism.Rel.and _ (instRelDenote I.D τ) :=
  RTy.andD_eq_rel I.D τ
theorem denote_orR : (Term.orR (Sig := Sig) τ).denote I env = @Classicism.Rel.or _ (instRelDenote I.D τ) :=
  RTy.orD_eq_rel I.D τ
theorem denote_coextR : (Term.coextR (Sig := Sig) τ).denote I env = @Classicism.Rel.coext _ (instRelDenote I.D τ) :=
  RTy.coextD_eq_rel I.D τ
theorem denote_boxR : (Term.boxR (Sig := Sig) τ).denote I env = @Classicism.Rel.boxAt _ (instRelDenote I.D τ) :=
  RTy.boxD_eq_rel I.D τ
theorem denote_inclR : (Term.inclR (Sig := Sig) τ).denote I env = @Classicism.Rel.incl _ (instRelDenote I.D τ) :=
  RTy.inclD_eq_rel I.D τ

end Term

end Classicism.Meta
